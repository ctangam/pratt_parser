struct Lexer {
    tokens: Vec<char>,
}

impl Lexer {
    fn new(input: &str) -> Self {
        let mut tokens = input
            .chars()
            .filter(|c| !c.is_ascii_whitespace())
            .collect::<Vec<_>>();
        tokens.reverse();
        Self { tokens }
    }

    fn next(&mut self) -> Option<char> {
        self.tokens.pop()
    }

    fn peek(&mut self) -> Option<char> {
        self.tokens.last().copied()
    }
}

use std::fmt;

enum S {
    Cons(char, Vec<S>),
}

impl fmt::Display for S {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            S::Cons(head, rest) => {
                if rest.is_empty(){
                    write!(f, "{}", head)
                } else {
                    write!(f, "({}", head)?;
                    for s in rest {
                        write!(f, " {}", s)?;
                    }
                    write!(f, ")")
                }
            }
        }
    }
}

fn expr(input: &str) -> S {
    let mut lexer = Lexer::new(input);
    expr_bp(&mut lexer, 0).unwrap()
}

fn expr_bp(lexer: &mut Lexer, min_bp: u8) -> Option<S> {
    let mut lhs = match lexer.peek() {
        Some('(') => {
            lexer.next();
            let lhs = expr_bp(lexer, 0).unwrap();
            assert_eq!(lexer.next(), Some(')'));
            Some(lhs)
        }
        _ => None,
    };

    loop {
        let token = match lexer.peek() {
            Some(token) => token,
            None => break,
        };

        if let Some((l_bp, r_bp)) = binding_power(token, lhs.is_none()) {
            if l_bp < min_bp {
                break;
            }
            lexer.next();
            let rhs = expr_bp(lexer, r_bp);
            let mut args = Vec::new();
            args.extend(lhs);
            args.extend(rhs);
            lhs = Some(S::Cons(token, args));

            continue;
        }

        break;
    }

    lhs
}

fn binding_power(op: char, prefix: bool) -> Option<(u8, u8)> {
    let res = match op {
        '0'..='9' | 'a'..='z' | 'A'..='Z' => (99, 100),
        '=' => (2, 1),
        '+' | '-' if prefix => (99, 9),
        '+' | '-' => (5, 6),
        '*' | '/' => (7, 8),
        '!' => (11, 100),
        '.' => (14, 13),
        _ => return None,
    };

    Some(res)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_expr_single_number() {
        let s = expr("1");
        assert_eq!(s.to_string(), "1");
    }

    #[test]
    fn test_expr_addition_and_multiplication() {
        let s = expr("1 + 2 * 3");
        assert_eq!(s.to_string(), "(+ 1 (* 2 3))");
    }

    #[test]
    fn test_expr_multiple_additions_and_multiplications() {
        let s = expr("a + b * c * d + e");
        assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");
    }

    #[test]
    fn test_expr_function_calls() {
        let s = expr("f . g . h");
        assert_eq!(s.to_string(), "(. f (. g h))");
    }

    #[test]
    fn test_expr_mixed_operations() {
        let s = expr(" 1 + 2 + f . g . h * 3 * 4");
        assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))");
    }

    #[test]
    fn test_expr_double_negation() {
        let s = expr("--1 * 2");
        assert_eq!(s.to_string(), "(* (- (- 1)) 2)");
    }

    #[test]
    fn test_expr_double_negation_function_call() {
        let s = expr("--f . g");
        assert_eq!(s.to_string(), "(- (- (. f g)))");
    }

    #[test]
    fn test_expr_negation_factorial() {
        let s = expr("-9!");
        assert_eq!(s.to_string(), "(- (! 9))");
    }

    #[test]
    fn test_expr_factorial() {
        let s = expr("3! * 4!");
        assert_eq!(s.to_string(), "(* (! 3) (! 4))");
    }

    #[test]
    fn test_expr_function_call_factorial() {
        let s = expr("f . g !");
        assert_eq!(s.to_string(), "(! (. f g))");
    }

    #[test]
    fn test_expr_nested_parentheses() {
        let s = expr("(((0)))");
        assert_eq!(s.to_string(), "0");
    }
}
