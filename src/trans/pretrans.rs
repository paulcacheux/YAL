use ast;
use ty;
use codemap::Spanned;
use errors::TranslationError;
use trans::{self, TranslationResult};
use trans::tables::Tables;
use std::collections::HashSet;

pub(super) fn translate_types(
    tables: &mut Tables,
    structs: Vec<ast::Struct>,
) -> TranslationResult<()> {
    // collect all names
    for s in &structs {
        if tables.types.pre_register_struct_type(s.name.clone()) {
            return error!(TranslationError::TypeAlreadyDefined(s.name.clone()), s.span);
        }
    }

    // really build structs
    for s in structs {
        let mut fields_set = HashSet::new();
        let mut fields = Vec::new();
        for &(ref name, ref aty) in &s.fields {
            let ty = trans::translate_type(&mut tables.types, aty.clone(), false)?;
            let field_name = name.inner.clone();
            if !fields_set.insert(field_name.clone()) {
                return error!(TranslationError::FieldAlreadyDefined(field_name), name.span);
            }
            fields.push((field_name, ty));
        }

        let tv = ty::TypeValue::Struct(ty::StructType {
            name: s.name.clone(),
            fields,
        });
        tables.types.register_struct_type(&s.name, tv);
    }

    Ok(())
}
