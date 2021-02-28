use hir::{known, AsName};
use ide_db::helpers::FamousDefs;
use stdx::format_to;
use syntax::{
    ast::{self, ArgListOwner, LoopBodyOwner},
    AstNode, Direction,
};

use crate::{AssistContext, AssistId, AssistKind, Assists};

// Assist: convert_for_to_iter_for_each
//
// Converts a for loop into a for_each loop on the Iterator.
//
// ```
// fn main() {
//     let x = vec![1, 2, 3];
//     for $0v in x {
//         let y = v * 2;
//     }
// }
// ```
// ->
// ```
// fn main() {
//     let x = vec![1, 2, 3];
//     x.into_iter().for_each(|v| {
//         let y = v * 2;
//     });
// }
// ```
pub(crate) fn convert_for_to_iter_for_each(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    let for_loop = ctx.find_node_at_offset::<ast::ForExpr>()?;
    let iterable = for_loop.iterable()?;
    let pat = for_loop.pat()?;
    let body = for_loop.loop_body()?;

    acc.add(
        AssistId("convert_for_to_iter_for_each", AssistKind::RefactorRewrite),
        "Convert a for loop into an Iterator::for_each",
        for_loop.syntax().text_range(),
        |builder| {
            let mut buf = String::new();

            if let Some((expr_behind_ref, method)) =
                is_ref_and_impls_iter_method(&ctx.sema, &iterable)
            {
                // We have either "for x in &col" and col implements a method called iter
                //             or "for x in &mut col" and col implements a method called iter_mut
                format_to!(buf, "{}.{}()", expr_behind_ref, method);
            } else if impls_core_iter(&ctx.sema, &iterable) {
                format_to!(buf, "{}", iterable);
            } else {
                if let ast::Expr::RefExpr(_) = iterable {
                    format_to!(buf, "({}).into_iter()", iterable);
                } else {
                    format_to!(buf, "{}.into_iter()", iterable);
                }
            }

            format_to!(buf, ".for_each(|{}| {});", pat, body);

            builder.replace(for_loop.syntax().text_range(), buf)
        },
    )
}

// Assist: convert_iter_for_each_to_for
//
// Converts a for_each on an Iterator to a for loop.
//
// ```
// //- /libcore.rs crate:core
// pub mod iter { pub mod traits { pub mod iterator {
//     pub trait Iterator {
//         type Item;
//         fn next(&mut self) -> Option<Self::Item>;
//      }
// }}}
// //- /main.rs crate:main deps:core
// struct X;
// impl core::iter::traits::iterator::Iterator for X {
//     type Item = ();
//     fn next(&mut self) -> Option<()> { None }
// }
// fn main() {
//     let x = X;
//     x.$0for_each(|v| {
//         let y = v * 2;
//     });
// }
// ```
// ->
// ```
// struct X;
// impl core::iter::traits::iterator::Iterator for X {
//     type Item = ();
//     fn next(&mut self) -> Option<()> { None }
// }
// fn main() {
//     let x = X;
//     for v in x {
//         let y = v * 2;
//     }
// }
// ```
pub(crate) fn convert_iter_for_each_to_for(acc: &mut Assists, ctx: &AssistContext) -> Option<()> {
    let method_call = ctx.find_node_at_offset::<ast::MethodCallExpr>()?;
    let recv = method_call.receiver()?;
    if !impls_core_iter(&ctx.sema, &recv) {
        return None;
    }

    let name = method_call.name_ref()?;
    if name.as_name() != known::for_each {
        return None;
    }

    let (param, body) = extract_only_param_closure(&method_call)?;

    acc.add(
        AssistId("convert_iter_for_each_to_for", AssistKind::RefactorRewrite),
        "Convert an Iterator::for_each to a for loop",
        method_call.syntax().text_range(),
        |builder| {
            let mut buf = String::new();
            format_to!(buf, "for {} in ", param);
            if !strip_into_iter_if_first_method_call(&ctx.sema, &mut buf, &method_call) {
                format_to!(buf, "{}", recv);
            }
            format_to!(buf, " {}", body);

            let syntax = method_call.syntax();
            let mut range = syntax.text_range();
            // If there's a semicolon after the for_each we need to get rid of that. Simplest way
            // is to extend the range to include it
            if let Some(node_or_tok) = syntax.next_sibling_or_token() {
                match node_or_tok.into_token() {
                    Some(tok) if tok.text() == ";" => {
                        range = syntax::TextRange::new(range.start(), tok.text_range().end());
                    }
                    _ => {}
                }
            }
            builder.replace(range, buf)
        },
    )
}

/// If iterable is a reference where the expression behind the reference implements a method
/// returning an Iterator called iter or iter_mut (depending on the type of reference) then return
/// the expression behind the reference and the method name
fn is_ref_and_impls_iter_method(
    sema: &hir::Semantics<ide_db::RootDatabase>,
    iterable: &ast::Expr,
) -> Option<(ast::Expr, hir::Name)> {
    let ref_expr = match iterable {
        ast::Expr::RefExpr(r) => r,
        _ => return None,
    };
    let wanted_method = if ref_expr.mut_token().is_some() { known::iter_mut } else { known::iter };
    let expr_behind_ref = ref_expr.expr()?;
    let typ = sema.type_of_expr(&expr_behind_ref)?;
    let scope = sema.scope(iterable.syntax());
    let krate = scope.module()?.krate();
    let traits_in_scope = scope.traits_in_scope();
    let iter_trait = FamousDefs(sema, Some(krate)).core_iter_Iterator()?;
    let has_wanted_method = typ.iterate_method_candidates(
        sema.db,
        krate,
        &traits_in_scope,
        Some(&wanted_method),
        |_, func| {
            if func.ret_type(sema.db).impls_trait(sema.db, iter_trait, &[]) {
                return Some(());
            }
            None
        },
    );
    has_wanted_method.and(Some((expr_behind_ref, wanted_method)))
}

fn impls_core_iter(sema: &hir::Semantics<ide_db::RootDatabase>, iterable: &ast::Expr) -> bool {
    let krate = get_crate(sema, iterable);
    let trt = if let Some(t) = FamousDefs(sema, krate).core_iter_Iterator() {
        t
    } else {
        return false;
    };
    impls_trait(sema, iterable, trt)
}

fn impls_core_into_iter(sema: &hir::Semantics<ide_db::RootDatabase>, expr: &ast::Expr) -> bool {
    let krate = get_crate(sema, expr);
    let trt = if let Some(t) = FamousDefs(sema, krate).core_iter_IntoIterator() {
        t
    } else {
        return false;
    };
    impls_trait(sema, expr, trt)
}

fn get_crate(sema: &hir::Semantics<ide_db::RootDatabase>, expr: &ast::Expr) -> Option<hir::Crate> {
    sema.scope(expr.syntax()).module().and_then(|m| Some(m.krate()))
}

fn impls_trait(
    sema: &hir::Semantics<ide_db::RootDatabase>,
    expr: &ast::Expr,
    trt: hir::Trait,
) -> bool {
    let typ = if let Some(t) = sema.type_of_expr(expr) {
        t
    } else {
        return false;
    };
    return typ.impls_trait(sema.db, trt, &[]);
}

/// Given a method call with a single closure parameter, return the single parameter to the closure
/// and the body of the closure
fn extract_only_param_closure(
    method_call: &ast::MethodCallExpr,
) -> Option<(ast::Param, ast::Expr)> {
    let mut args = method_call.arg_list()?.args();
    let first_arg = args.next()?;
    if args.next().is_some() {
        return None;
    }
    let closure = match first_arg {
        ast::Expr::ClosureExpr(c) => c,
        _ => return None,
    };
    let mut params = closure.param_list()?.params();
    let param = params.next()?;
    if params.next().is_some() {
        return None;
    }
    Some((param, closure.body()?))
}

/// If into_iter is the first method call then skip it when writing to buf, and also omit the final
/// method call. Otherwise leave buf alone.
/// Eg x.into_iter().take(1).for_each() -> x.take(1)
fn strip_into_iter_if_first_method_call(
    sema: &hir::Semantics<ide_db::RootDatabase>,
    buf: &mut String,
    method_call: &ast::MethodCallExpr,
) -> bool {
    let mut call = method_call.clone();
    // Find the left-most method call
    let last_call = loop {
        match call.receiver() {
            Some(ast::Expr::MethodCallExpr(c)) => call = c,
            _ => break call,
        }
    };

    let last_method_name = match last_call.name_ref() {
        Some(n) => n.as_name(),
        _ => return false,
    };
    let recv = match last_call.receiver() {
        Some(r) => r,
        _ => return false,
    };
    if last_method_name != known::into_iter || !impls_core_into_iter(sema, &recv) {
        return false;
    }

    format_to!(buf, "{}", recv);

    let method_call_range = method_call.syntax().text_range();
    for syn in last_call.syntax().siblings_with_tokens(Direction::Next).skip(1) {
        // We want to omit method_call so append to buf until we're at the "." token inside of method_call
        if let Some(ref t) = syn.clone().into_token() {
            if t.text() == "." && method_call_range.contains_range(t.text_range()) {
                return true;
            }
        }
        format_to!(buf, "{}", syn);
    }
    true
}

#[cfg(test)]
mod tests {
    use crate::tests::{check_assist, check_assist_not_applicable};

    use super::*;

    const EMPTY_ITER_FIXTURE: &'static str = r"
//- /lib.rs deps:core crate:empty_iter
pub struct EmptyIter;
impl Iterator for EmptyIter {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> { None }
}

pub struct Empty;
impl Empty {
    pub fn iter(&self) -> EmptyIter { EmptyIter }
    pub fn iter_mut(&self) -> EmptyIter { EmptyIter }
}

impl IntoIterator for Empty {
    type Item = usize;
    type IntoIter = EmptyIter;
    fn into_iter(self) -> EmptyIter { EmptyIter }
}

pub struct NoIterMethod;
";

    fn check_assist_with_fixtures(assist: crate::handlers::Handler, before: &str, after: &str) {
        let before = &format!(
            "//- /main.rs crate:main deps:core,empty_iter{}{}{}",
            before,
            FamousDefs::FIXTURE,
            EMPTY_ITER_FIXTURE
        );
        check_assist(assist, before, after);
    }

    #[test]
    fn test_f2i_not_for() {
        check_assist_not_applicable(
            convert_for_to_iter_for_each,
            r"
let mut x = vec![1, 2, 3];
x.iter_mut().$0for_each(|v| *v *= 2);
        ",
        )
    }

    #[test]
    fn test_f2i_simple_for() {
        check_assist(
            convert_for_to_iter_for_each,
            r"
fn main() {
    let x = vec![1, 2, 3];
    for $0v in x {
        v *= 2;
    }
}",
            r"
fn main() {
    let x = vec![1, 2, 3];
    x.into_iter().for_each(|v| {
        v *= 2;
    });
}",
        )
    }

    #[test]
    fn test_f2i_for_borrowed() {
        check_assist_with_fixtures(
            convert_for_to_iter_for_each,
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    for $0v in &x {
        let a = v * 2;
    }
}
",
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    x.iter().for_each(|v| {
        let a = v * 2;
    });
}
",
        )
    }

    #[test]
    fn test_f2i_for_borrowed_no_iter_method() {
        check_assist_with_fixtures(
            convert_for_to_iter_for_each,
            r"
use empty_iter::*;
fn main() {
    let x = NoIterMethod;
    for $0v in &x {
        let a = v * 2;
    }
}
",
            r"
use empty_iter::*;
fn main() {
    let x = NoIterMethod;
    (&x).into_iter().for_each(|v| {
        let a = v * 2;
    });
}
",
        )
    }

    #[test]
    fn test_f2i_for_borrowed_mut() {
        check_assist_with_fixtures(
            convert_for_to_iter_for_each,
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    for $0v in &mut x {
        let a = v * 2;
    }
}
",
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    x.iter_mut().for_each(|v| {
        let a = v * 2;
    });
}
",
        )
    }

    #[test]
    fn test_f2i_for_borrowed_mut_behind_var() {
        check_assist(
            convert_for_to_iter_for_each,
            r"
fn main() {
    let x = vec![1, 2, 3];
    let y = &mut x;
    for $0v in y {
        *v *= 2;
    }
}",
            r"
fn main() {
    let x = vec![1, 2, 3];
    let y = &mut x;
    y.into_iter().for_each(|v| {
        *v *= 2;
    });
}",
        )
    }

    #[test]
    fn test_f2i_already_impls_iterator() {
        check_assist_with_fixtures(
            convert_for_to_iter_for_each,
            r#"
use empty_iter::*;
fn main() {
    let x = Empty;
    for$0 a in x.iter().take(1) {
    }
}
"#,
            r#"
use empty_iter::*;
fn main() {
    let x = Empty;
    x.iter().take(1).for_each(|a| {
    });
}
"#,
        );
    }

    #[test]
    fn test_i2f_not_iterator() {
        check_assist_not_applicable(
            convert_iter_for_each_to_for,
            r"
struct Foo;

fn main() {
    let f = Foo;
    f.iter().$0for_each(|x| {});
}
",
        );
    }

    #[test]
    fn test_i2f_simple_trailing_semicolon() {
        check_assist_with_fixtures(
            convert_iter_for_each_to_for,
            r"
use empty_iter::*;
fn main() {
    let x = EmptyIter;
    x.$0for_each(|v| {
        let y = v * 2;
    });
}
",
            r"
use empty_iter::*;
fn main() {
    let x = EmptyIter;
    for v in x {
        let y = v * 2;
    }
}
",
        );
    }

    #[test]
    fn test_i2f_simple() {
        check_assist_with_fixtures(
            convert_iter_for_each_to_for,
            r"
use empty_iter::*;
fn main() {
    let x = EmptyIter;
    x.$0for_each(|v| {
        let y = v * 2;
    })
}
",
            r"
use empty_iter::*;
fn main() {
    let x = EmptyIter;
    for v in x {
        let y = v * 2;
    }
}
",
        );
    }

    #[test]
    fn test_i2f_complex() {
        check_assist_with_fixtures(
            convert_iter_for_each_to_for,
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    x.iter().$0for_each(|v| {
        let y = v * 2;
    });
}
",
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    for v in x.iter() {
        let y = v * 2;
    }
}
",
        );
    }

    #[test]
    fn test_i2f_into_iter() {
        check_assist_with_fixtures(
            convert_iter_for_each_to_for,
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    x.into_iter().$0for_each(|v| {
        let y = v * 2;
    });
}
",
            r"
use empty_iter::*;
fn main() {
    let x = Empty;
    for v in x {
        let y = v * 2;
    }
}
",
        );
    }
}
