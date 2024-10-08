use clippy_utils::diagnostics::span_lint_and_then;
use clippy_utils::visitors::{for_each_expr, for_each_expr_without_closures, Descend, Visitable};
use core::ops::ControlFlow::Continue;
use hir::def::{DefKind, Res};
use hir::{BlockCheckMode, ExprKind, QPath, Safety, UnOp};
use rustc_ast::Mutability;
use rustc_hir as hir;
use rustc_lint::{LateContext, LateLintPass};
use rustc_middle::lint::in_external_macro;
use rustc_middle::ty;
use rustc_session::declare_lint_pass;
use rustc_span::{DesugaringKind, Span};

declare_clippy_lint! {
    /// ### What it does
    /// This lint checks for unsafe operations and suggests to wrap them in individual unsafe blocks.
    #[clippy::version = "1.83.0"]
    pub FOO_FUNCTIONS,
    restriction,
    "default lint description"
}

declare_lint_pass!(FooFunctions => [FOO_FUNCTIONS]);

impl<'tcx> LateLintPass<'tcx> for FooFunctions {
    fn check_block(&mut self, cx: &LateContext<'tcx>, block: &'tcx hir::Block<'_>) {
        if !matches!(block.rules, BlockCheckMode::UnsafeBlock(_))
            || in_external_macro(cx.tcx.sess, block.span)
            || block.span.is_desugaring(DesugaringKind::Await)
        {
            return;
        }

        let mut unsafe_ops = vec![];
        let state_num = block.stmts.len();
        collect_unsafe_exprs(cx, block, &mut unsafe_ops);
        
        if unsafe_ops.is_empty() {
            span_lint_and_then(
                cx,
                FOO_FUNCTIONS,
                block.span,
                format!(
                    "this `unsafe` block is useless, unsafe_block_spans:{:?}",
                    block.span,
                ),
                |diag| {
                        diag.span_note(block.span, format!(
                            "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}",
                            block.span,
                        ));
                },
            );
        }

        if unsafe_ops.len() == 1 {
            if state_num > 1 {
                let (msg, span) = unsafe_ops.get(0).unwrap();
                span_lint_and_then(
                    cx,
                    FOO_FUNCTIONS,
                    block.span,
                    format!(
                        "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}, unsafe_op_span:{:?}",
                        block.span,
                        span
                    ),
                    |diag| {
                        for (msg, span) in &unsafe_ops { 
                            diag.span_note(*span, format!(
                                "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}, unsafe_op_span:{:?}",
                                block.span,
                                span
                            ));
                        }
                    },
                );
            } else if state_num == 1 {
                // TODO:处理仅有一个 unsafe 操作的情况
                let st=block.stmts.get(0);
                match st.unwrap().kind {
                    hir::StmtKind::Expr(expr) => {
                        match expr.kind {
                            ExprKind::If(_, then_block, else_block) => {
                                let then_count = match then_block.kind {
                                    ExprKind::Block(ref block, _) => block.stmts.len(),
                                    _ => 0,
                                };
                                let else_count = match else_block.unwrap().kind {
                                    ExprKind::Block(ref block, _) => block.stmts.len(),
                                    _ => 0,
                                };

                                if then_count > 1 || else_count > 1 {
                                    span_lint_and_then(
                                        cx,
                                        FOO_FUNCTIONS,
                                        block.span,
                                        format!(
                                            "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}",
                                            block.span,
                                        ),
                                        |diag| {
                                                diag.span_note(block.span, format!(
                                                    "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}",
                                                    block.span,
                                                ));
                                        },
                                    );
                                }
                            },
                            ExprKind::Loop(e, _, _, _) => {
                                let count=e.stmts.len();
                                if count>1{
                                    span_lint_and_then(
                                        cx,
                                        FOO_FUNCTIONS,
                                        block.span,
                                        format!(
                                            "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}",
                                            block.span,
                                        ),
                                        |diag| {
                                                diag.span_note(block.span, format!(
                                                    "this `unsafe` block contains overscoped unsafe block, unsafe_block_spans:{:?}",
                                                    block.span,
                                                ));
                                        },
                                    );
                                }
                            },
                             _=>{}
                        }
                    }
                    _=>{}
                }

            }
        }

        if unsafe_ops.len() > 1 {
            span_lint_and_then(
                cx,
                FOO_FUNCTIONS,
                block.span,
                format!(
                    "this `unsafe` block contains overscoped unsafe block, unsafe_ops:{}",
                    unsafe_ops.len()
                ),
                |diag| {
                    for (msg, span) in &unsafe_ops { 
                        diag.span_note(*span, *msg);
                    }
                },
            );
        }
    }
}


fn collect_unsafe_exprs<'tcx>(
    cx: &LateContext<'tcx>,
    node: impl Visitable<'tcx>,
    unsafe_ops: &mut Vec<(&'static str, Span)>,
) {
    for_each_expr(cx, node, |expr| {
        match expr.kind {
            ExprKind::InlineAsm(_) => unsafe_ops.push(("inline assembly used here", expr.span)),
            ExprKind::Field(e, _) => {
                if cx.typeck_results().expr_ty(e).is_union() {
                    unsafe_ops.push(("union field access occurs here", expr.span));
                }
            },
            ExprKind::Path(QPath::Resolved(_, hir::Path { res: Res::Def(DefKind::Static { mutability: Mutability::Mut, .. }, _), .. })) => {
                unsafe_ops.push(("access of a mutable static occurs here", expr.span));
            },
            ExprKind::Unary(UnOp::Deref, e) if cx.typeck_results().expr_ty_adjusted(e).is_unsafe_ptr() => {
                unsafe_ops.push(("raw pointer dereference occurs here", expr.span));
            },
            ExprKind::Call(path_expr, _) => {
                let sig = match *cx.typeck_results().expr_ty(path_expr).kind() {
                    ty::FnDef(id, _) => cx.tcx.fn_sig(id).skip_binder(),
                    ty::FnPtr(sig_tys, hdr) => sig_tys.with(hdr),
                    _ => return Continue(Descend::Yes),
                };
                if sig.safety() == Safety::Unsafe {
                    unsafe_ops.push(("unsafe function call occurs here", expr.span));
                }
            },
            ExprKind::MethodCall(..) => {
                if let Some(sig) = cx.typeck_results().type_dependent_def_id(expr.hir_id).map(|def_id| cx.tcx.fn_sig(def_id)) {
                    if sig.skip_binder().safety() == Safety::Unsafe {
                        unsafe_ops.push(("unsafe method call occurs here", expr.span));
                    }
                }
            },
            _ => {}
        };

        Continue::<(), _>(Descend::Yes)
    });
}
