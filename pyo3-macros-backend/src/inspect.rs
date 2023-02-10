//! Generates static structures for runtime inspection of the Python objects
//!
//! The goal is to enable Rust code to implement features similar to Python's `dict(obj)`.
//! The generated structures are read-only.

use proc_macro2::{Ident, Literal, TokenStream, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::spanned::Spanned;
use syn::Type;
use crate::method::FnType;
use crate::pyclass::{FieldPyO3Options, get_class_python_name};
use crate::PyClassArgs;
use crate::pymethod::PyMethod;

pub(crate) fn generate_class_fields(
    cls: &Ident,
    args: &PyClassArgs,
    field_options: &Vec<(&syn::Field, FieldPyO3Options)>,
) -> Vec<TokenStream> {
    let ident_prefix = format_ident!("_path_{}", cls);
    let class_field_info = format_ident!("{}_struct_field_info", ident_prefix);
    let class_info = format_ident!("{}_struct_info", ident_prefix);

    let name = Literal::string(&*get_class_python_name(cls, args).to_string());

    let mut fields: Vec<TokenStream> = vec![];
    for (field, options) in field_options {
        let typ = generate_type(cls.to_string().as_str(), &field.ty)
            .map(|it| Box::new(it) as Box<dyn ToTokens>)
            .unwrap_or_else(|| Box::new(cls));
        let name = options.name.as_ref()
            .map(|it| Literal::string(&*it.value.0.to_string()))
            .or_else(|| field.ident.as_ref().map(|it| Literal::string(&*it.to_string())));

        if let Some(name) = name {
            if options.get.is_some() {
                fields.push(quote! {
                    &_pyo3::inspect::fields::FieldInfo {
                        name: #name,
                        kind: _pyo3::inspect::fields::FieldKind::Getter,
                        py_type: ::std::option::Option::Some(|| (&&&_pyo3::inspect::types::Typed::<#typ>::new()).type_output()),
                        arguments: &[],
                    }
                });
            }

            if options.set.is_some() {
                fields.push(quote! {
                    &_pyo3::inspect::fields::FieldInfo {
                        name: #name,
                        kind: _pyo3::inspect::fields::FieldKind::Setter,
                        py_type: ::std::option::Option::Some(|| _pyo3::inspect::types::TypeInfo::None),
                        arguments: &[
                            _pyo3::inspect::fields::ArgumentInfo {
                                name: #name,
                                kind: _pyo3::inspect::fields::ArgumentKind::Position,
                                py_type: ::std::option::Option::Some(|| (&&&_pyo3::inspect::types::Type::<#typ>::new()).type_output()),
                                default_value: false,
                                is_modified: false,
                            }
                        ],
                    }
                });
            }
        }
    }
    fields
}
/// Extracts inspection information from the `#[pyclass]` macro.
///
/// Extracted information:
/// - Name of the class
pub(crate) fn generate_class_inspection(
    cls: &Ident,
    args: &PyClassArgs,
    field_options: &Vec<(&syn::Field, FieldPyO3Options)>,
) -> TokenStream {
    let ident_prefix = format_ident!("_path_{}", cls);
    let class_field_info = format_ident!("{}_struct_field_info", ident_prefix);
    let class_info = format_ident!("{}_struct_info", ident_prefix);

    let name = Literal::string(&*get_class_python_name(cls, args).to_string());

    let mut fields: Vec<TokenStream> = vec![];
    for (field, options) in field_options {
        let typ = generate_type(cls.to_string().as_str(), &field.ty)
            .map(|it| Box::new(it) as Box<dyn ToTokens>)
            .unwrap_or_else(|| Box::new(cls));
        let name = options.name.as_ref()
            .map(|it| Literal::string(&*it.value.0.to_string()))
            .or_else(|| field.ident.as_ref().map(|it| Literal::string(&*it.to_string())));

        if let Some(name) = name {
            if options.get.is_some() {
                fields.push(quote! {
                    &_pyo3::inspect::fields::FieldInfo {
                        name: #name,
                        kind: _pyo3::inspect::fields::FieldKind::Getter,
                        py_type: ::std::option::Option::Some(|| {
                            use _pyo3::inspect::types::{WithTypeInfo, WithCustomTypeInfo};
                            (&&&_pyo3::inspect::types::Typed::<#typ>::new()).type_output()
                        }),
                        arguments: &[],
                    }
                });
            }

            if options.set.is_some() {
                fields.push(quote! {
                    &_pyo3::inspect::fields::FieldInfo {
                        name: #name,
                        kind: _pyo3::inspect::fields::FieldKind::Setter,
                        py_type: ::std::option::Option::Some(|| _pyo3::inspect::types::TypeInfo::None),
                        arguments: &[
                            _pyo3::inspect::fields::ArgumentInfo {
                                name: #name,
                                kind: _pyo3::inspect::fields::ArgumentKind::Position,
                                py_type: ::std::option::Option::Some(||{
                                    use _pyo3::inspect::types::{WithTypeInfo, WithCustomTypeInfo};
                                    (&&&_pyo3::inspect::types::Typed::<#typ>::new()).type_output()
                                    }),
                                default_value: false,
                                is_modified: false,
                            }
                        ],
                    }
                });
            }
        }
    }

    let field_size = Literal::usize_suffixed(fields.len());

    quote! {
        const #class_field_info: [&'static _pyo3::inspect::fields::FieldInfo<'static>; #field_size] = [
            #(#fields),*
        ];

        const #class_info: _pyo3::inspect::classes::ClassStructInfo<'static> = _pyo3::inspect::classes::ClassStructInfo {
            name: #name,
            base: ::std::option::Option::None, //TODO
            fields: &#class_field_info,
        };

        impl _pyo3::inspect::classes::InspectStruct<'static> for #cls {
            fn inspect_struct() -> &'static _pyo3::inspect::classes::ClassStructInfo<'static> {
                &#class_info
            }
        }
    }
}

/// Extracts information from an impl block annotated with `#[pymethods]`.
///
/// Currently, generating information from multiple impl blocks for the same class is not possible
/// (name collision in the generated structures and trait implementation), which makes inspection incompatible
/// with `multiple-pymethods`.
pub(crate) fn generate_impl_inspection(
    cls: &Type,
    fields: Vec<Ident>
) -> TokenStream {
    let ident_prefix = generate_unique_ident(cls, None);
    let fields_info = format_ident!("{}_fields_info", ident_prefix);

    let field_size = Literal::usize_suffixed(fields.len());

    let fields = fields.iter()
        .map(|field| quote!(&#field));

    quote! {
        const #fields_info: [&'static _pyo3::inspect::fields::FieldInfo<'static>; #field_size] = [
            #(#fields),*
        ];

        impl _pyo3::inspect::classes::InspectImpl<'static> for #cls {
            fn inspect_impl() -> &'static [&'static _pyo3::inspect::fields::FieldInfo<'static>] {
                &#fields_info
            }
        }
    }
}

/// Generates information from a field in a `#[pymethods]` block.
///
/// Extracted information:
/// - Field name
/// - Field kind (getter / setter / constructor / function / static method / …)
pub(crate) fn generate_fields_inspection(
    cls: &Type,
    field: &PyMethod<'_>
) -> (TokenStream, Ident) {
    let class_name = match cls {
        Type::Path(path) => {
            path.path.segments.iter().map(|s| s.ident.to_string()).reduce(|x, y| x + &y).unwrap()
        }
        _ => unreachable!()
    };

    let ident_prefix = generate_unique_ident(cls, Some(field.spec.name));

    let field_info_name = format_ident!("{}_info", ident_prefix);
    let field_args_name = format_ident!("{}_args", ident_prefix);
    let field_type_fn_name = format_ident!("{}_output_fn", ident_prefix);

    let field_name = TokenTree::Literal(Literal::string(&*field.method_name));
    let field_kind = match &field.spec.tp {
        FnType::Getter(_) => quote!(_pyo3::inspect::fields::FieldKind::Getter),
        FnType::Setter(_) => quote!(_pyo3::inspect::fields::FieldKind::Setter),
        FnType::Fn(_) => quote!(_pyo3::inspect::fields::FieldKind::Function),
        FnType::FnNew => quote!(_pyo3::inspect::fields::FieldKind::New),
        FnType::FnClass => quote!(_pyo3::inspect::fields::FieldKind::ClassMethod),
        FnType::FnStatic => quote!(_pyo3::inspect::fields::FieldKind::StaticMethod),
        FnType::FnModule => todo!("FnModule is not currently supported"),
        FnType::ClassAttribute => quote!(_pyo3::inspect::fields::FieldKind::ClassAttribute),
    };
    let field_type = if !matches!(&field.spec.output, Type::Infer(_)) {
        generate_type(&class_name, &field.spec.output)
            .map(|it| it.to_token_stream())
            .unwrap_or_else(|| cls.to_token_stream())
    } else {
        quote! {()}
    };

    let mut args: Vec<TokenStream> = vec![];
    for arg in &field.spec.signature.arguments {
        let name = Literal::string(&*arg.name.to_string());
        let typ = generate_type(&class_name, arg.ty)
            .map(|it| it.to_token_stream())
            .unwrap_or_else(|| cls.to_token_stream());

        let is_mutable = arg.mutability.is_some();

        if &*arg.name.to_string() != "py" {
            args.push(quote! {
                _pyo3::inspect::fields::ArgumentInfo {
                    name: #name,
                    kind: _pyo3::inspect::fields::ArgumentKind::PositionOrKeyword, //TODO
                    py_type: ::std::option::Option::Some(|| {
                        use _pyo3::inspect::types::{WithTypeInfo, WithCustomTypeInfo};
                        (&&&_pyo3::inspect::types::Typed::<#typ>::new()).type_input()
                    }),
                    default_value: false,
                    is_modified: #is_mutable,
                }
            });
        }
    }
    let args_size = Literal::usize_suffixed(args.len());

    let output = quote! {

        fn #field_type_fn_name() -> _pyo3::inspect::types::TypeInfo {
            use _pyo3::inspect::types::{WithTypeInfo, WithCustomTypeInfo};
            (&&&_pyo3::inspect::types::Typed::<#field_type>::new()).type_output()
        }

        const #field_args_name: [_pyo3::inspect::fields::ArgumentInfo<'static>; #args_size] = [
             #(#args),*
        ];

        const #field_info_name: _pyo3::inspect::fields::FieldInfo<'static> = _pyo3::inspect::fields::FieldInfo {
            name: #field_name,
            kind: #field_kind,
            py_type: ::std::option::Option::Some(#field_type_fn_name),
            arguments: &#field_args_name,
        };
    };

    (output, field_info_name)
}

fn generate_type(cls: &str, target: &Type) -> Option<Type> {
    use syn::punctuated::*;
    use syn::*;
    match target {
        Type::Path(path)
            if path
                .path
                .get_ident()
                .filter(|i| i.to_string() == "Self")
                .is_some() =>
        {
            Some(Type::Path(TypePath {
                qself: None,
                path: Path {
                    leading_colon: None,
                    segments: IntoIterator::into_iter([PathSegment {
                        ident: format_ident!("{}", cls),
                        arguments: PathArguments::None,
                    }])
                    .collect(),
                },
            }))
        }
        Type::Path(TypePath {
            qself,
            path: Path {
                leading_colon,
                segments,
            },
        }) => Some(Type::Path(TypePath {
            qself: qself.clone(),
            path: Path {
                leading_colon: leading_colon.clone(),
                segments: segments
                    .iter()
                    .map(|x| match x {
                        PathSegment { ident, arguments } => PathSegment {
                            ident: ident.clone(),
                            arguments: match arguments {
                                PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                                    colon2_token,
                                    lt_token,
                                    args,
                                    gt_token,
                                }) => {
                                    PathArguments::AngleBracketed(AngleBracketedGenericArguments {
                                        colon2_token: colon2_token.clone(),
                                        lt_token: lt_token.clone(),
                                        args: args
                                            .clone()
                                            .iter()
                                            .map(|t| match t {
                                                GenericArgument::Type(t) => GenericArgument::Type(
                                                    generate_type(cls, t).unwrap(),
                                                ),
                                                o => o.clone(),
                                            })
                                            .collect(),

                                        gt_token: gt_token.clone(),
                                    })
                                }
                                o => o.clone(),
                            },
                        },
                    })
                    .collect(),
            },
        })),
        Type::Reference(syn::TypeReference {
            and_token,
            lifetime: _,
            mutability,
            elem,
        }) => Some(Type::Reference(syn::TypeReference {
            and_token: *and_token,
            lifetime: None,
            mutability: *mutability,
            elem: Box::new(generate_type(cls, elem)?),
        })),
        other => Some(other.clone()),
    }
}

/// Generates a unique identifier based on a type and (optionally) a field.
///
/// For the same input values, the result should be the same output, and for different input values,
/// the output should be different. No other guarantees are made (do not try to parse it).
fn generate_unique_ident(class: &Type, field: Option<&Ident>) -> Ident {
    let span = if let Some(field) = field {
        field.span()
    } else {
        class.span()
    };

    let mut result = "".to_string();

    // Attempt to generate something unique for each type
    // Types that cannot be annotated with #[pyclass] are ignored
    match class {
        Type::Array(_) => unreachable!("Cannot generate a unique name for an array: {:?}", class),
        Type::BareFn(_) => unreachable!("Cannot generate a unique name for a function: {:?}", class),
        Type::Group(_) => unreachable!("Cannot generate a unique name for a group: {:?}", class),
        Type::ImplTrait(_) => unreachable!("Cannot generate a unique name for an impl trait: {:?}", class),
        Type::Infer(_) => unreachable!("Cannot generate a unique name for an inferred type: {:?}", class),
        Type::Macro(_) => unreachable!("Cannot generate a unique name for a macro: {:?}", class),
        Type::Never(_) => {
            result += "_never";
        },
        Type::Paren(_) => unreachable!("Cannot generate a unique name for a type in parenthesis: {:?}", class),
        Type::Path(path) => {
            result += "_path";
            for segment in &path.path.segments {
                result += "_";
                result += &*segment.ident.to_string();
            }
        }
        Type::Ptr(_) => unreachable!("Cannot generate a unique name for a pointer: {:?}", class),
        Type::Reference(_) => unreachable!("Cannot generate a unique name for a reference: {:?}", class),
        Type::Slice(_) => unreachable!("Cannot generate a unique name for a slice: {:?}", class),
        Type::TraitObject(_) => unreachable!("Cannot generate a unique name for a trait object: {:?}", class),
        Type::Tuple(_) => unreachable!("Cannot generate a unique name for a tuple: {:?}", class),
        _ => unreachable!("Cannot generate a unique name for an unknown type: {:?}", class),
    }

    if let Some(field) = field {
        result += "_";
        result += &*field.to_string()
    }

    Ident::new(&*result, span)
}
