use clippy_utils::macros::{find_format_arg_expr, find_format_args, root_macro_call_first_node};
use clippy_utils::source::{snippet_opt, indent_of};
use clippy_utils::{get_parent_as_impl, path_to_local_id};
use clippy_utils::diagnostics::span_lint_and_then;
use rustc_ast;
use rustc_data_structures::fx::FxHashMap;
use rustc_errors::Applicability;
use rustc_hir::*;
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::{declare_tool_lint, impl_lint_pass};
use rustc_span::{Span, sym};

declare_clippy_lint! {
    /// ### What it does
    ///
    /// ### Why is this bad?
    ///
    /// ### Example
    /// ```rust
    /// // example code where clippy issues a warning
    /// ```
    /// Use instead:
    /// ```rust
    /// // example code which does not raise clippy warning
    /// ```
    #[clippy::version = "1.73.0"]
    pub DERIVE_MORE_DISPLAY,
    nursery,
    "default lint description"
}
impl_lint_pass!(DeriveMoreDisplay => [DERIVE_MORE_DISPLAY]);

#[derive(Clone, Default)]
pub struct ImplementationToRemove {
    existing_display_impl: Option<(String, Vec<String>, Span)>,
    existing_item_span: Option<Span>,
}

#[derive(Clone, Default)]
pub struct DeriveMoreDisplay {
    pub replace_table: FxHashMap<HirId, ImplementationToRemove>,
    pub outer_span: Option<Span>,
}

impl LateLintPass<'_> for DeriveMoreDisplay {
    fn check_crate_post(&mut self, cx: &LateContext<'_>) {
        use itertools::Itertools;
        for ((format_string, arguments, impl_span), item_span) in self.replace_table
            .drain()
            .map(|(_, value)| value)
            .filter_map(|ImplementationToRemove { existing_display_impl, existing_item_span: existing_item }| existing_display_impl.zip(existing_item)) {
            let item_indent = indent_of(cx, item_span).unwrap_or(0);
            span_lint_and_then(
                cx,
                DERIVE_MORE_DISPLAY,
                impl_span,
                "this `impl` can be derived",
                |diag| {
                    diag.span_suggestion_hidden(
                        impl_span,
                        "remove the manual implementation...",
                        String::new(),
                        Applicability::MachineApplicable
                    );
                    diag.span_suggestion(
                        item_span.shrink_to_lo(),
                        "...and instead derive it...",
                        format!("\
                            #[derive(derive_more::Display)]\n\
                            {indent}#[display(\"{format_string}\"{arguments})]\n\
                            {indent}",
                            indent = " ".repeat(item_indent),
                            arguments = arguments.iter().format_with("", |argument, f| f(&format_args!(", \"{argument}\"")))
                        ),
                        Applicability::MachineApplicable
                    );
                }
            );
        }
    }

    fn check_impl_item(&mut self, cx: &LateContext<'_>, impl_item: &ImplItem<'_>) {
        if let Some((hir_id, format_string, arguments)) = applicable_display_implementation_to_new_format_string(cx, impl_item) {
            self.replace_table.entry(hir_id).or_default().existing_display_impl = Some((format_string, arguments, self.outer_span.unwrap()));
        }
    }

    fn check_item(&mut self, _cx: &LateContext<'_>, item: &Item<'_>) {
        if let ItemKind::Struct(_, _) = item.kind {
            self.replace_table.entry(item.hir_id()).or_default().existing_item_span = Some(item.span.shrink_to_lo());
        } else if let ItemKind::Impl(_) = item.kind {
            self.outer_span = Some(item.span);
        }
    }
}

fn find_field_expr_root<'a>(leaf: &'a Expr<'a>) -> &'a Expr<'a> {
    if let ExprKind::Field(object, _) = leaf.kind {
        find_field_expr_root(object)
    } else {
        leaf
    }
}

fn applicable_display_implementation_to_new_format_string(
    cx: &LateContext<'_>,
    impl_item: &ImplItem<'_>,
) -> Option<(HirId, String, Vec<String>)> {
    if_chain! {
        if impl_item.ident.name == sym::fmt;
        if let ImplItemKind::Fn(_, body_id) = impl_item.kind;
        if let Some(Impl { of_trait: Some(trait_ref), self_ty, .. }) = get_parent_as_impl(cx.tcx, impl_item.hir_id());
        if let TyKind::Path(path) = self_ty.kind;
        if let Some(trait_def_id) = trait_ref.trait_def_id();
        if let Some(sym::Display) = cx.tcx.get_diagnostic_name(trait_def_id);
        let res = cx.qpath_res(&path, self_ty.hir_id);
        if let Some(def_id) = res.opt_def_id();
        if def_id.krate == def_id::LOCAL_CRATE;
        let body = cx.tcx.hir().body(body_id);
        if let Some(self_argument) = body.params.get(0);
        if let Some(formatter_argument) = body.params.get(1);
        if let ExprKind::Block(Block { stmts: [], expr: Some(expr), .. }, _) = body.value.kind;
        if let ExprKind::MethodCall(_, object, _, _) = expr.kind;
        if path_to_local_id(object, formatter_argument.pat.hir_id);
        if let Some(macro_call) = root_macro_call_first_node(cx, *expr);
        if cx.tcx.get_diagnostic_name(macro_call.def_id) == Some(sym::write_macro);

        then {
            let mut return_value: Option<_> = None;
            find_format_args(cx, expr, macro_call.expn, |format_args| {
                if_chain! {
                    if let Ok(normal_arguments_of_self_fields) = format_args.arguments.all_args().iter().map(|argument| {
                        if_chain! {
                            if matches!(argument.kind, rustc_ast::format::FormatArgumentKind::Normal);
                            if let Ok(format_arg) = find_format_arg_expr(expr, &argument);
                            let field_root = find_field_expr_root(format_arg);
                            if path_to_local_id(field_root, self_argument.pat.hir_id);
                            if let Some(format_arg_snippet) = snippet_opt(cx, format_arg.span);
                            then {
                                Ok(format_arg_snippet)
                            } else {
                                Err(())
                            }
                        }
                    }).collect::<Result<Vec<_>, _>>();
                    if let Some(format_string_snippet) = snippet_opt(cx, format_args.span);
                    then {
                        return_value = Some((format_string_snippet.trim_matches('"').to_owned(), normal_arguments_of_self_fields));
                    }
                }
            });
            let local_def_id = def_id::LocalDefId { local_def_index: def_id.index };
            let hir_id = cx.tcx.hir().local_def_id_to_hir_id(local_def_id);
            return_value.map(|(format_string, arguments)| (hir_id, format_string, arguments))
        } else {
            None
        }
    }
}
