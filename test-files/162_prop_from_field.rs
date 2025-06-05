pub struct From<'a> {
    pub original: &'a (),
    pub span: (),
}
pub struct Attrs<'a> {
    pub from: Option<From<'a>>,
}

pub struct Field<'a> {
    pub attrs: Attrs<'a>,
}

fn from_field<'a, 'b>(fields: &'a [Field<'b>]) -> Option<&'a Field<'b>> {
    for field in fields {
        if field.attrs.from.is_some() {
            return Some(field);
        }
    }
    None
}

fn main(){}
