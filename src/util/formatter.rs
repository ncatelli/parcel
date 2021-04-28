pub trait Formatter<'a, A, B> {
    fn format(&self, input: A) -> Result<A, String>;
}
