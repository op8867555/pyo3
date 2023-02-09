use crate::{impl_::pyclass::PyClassImpl, inspect::fields::FieldInfo, PyTypeInfo};

/// Information about a Python class.
#[derive(Debug)]
pub struct ClassInfo {
    /// Base information about the class.
    pub class: ClassStructInfo,

    /// Information found in `#[pymethods]`.
    pub fields: Vec<&'static FieldInfo<'static>>,
}

/// Subset of available information about a Python class, including only what is available by parsing the `#[pyclass]`
/// block (methods are missing).
#[derive(Debug)]
pub struct ClassStructInfo {
    pub name: &'static str,
    pub base: Option<&'static str>,
    pub fields: Vec<&'static FieldInfo<'static>>,
}

impl ClassInfo {
    /// The Python name of this class.
    pub fn name(&self) -> &str {
        self.class.name
    }

    /// The Python's base class.
    pub fn base(&self) -> Option<&'static str> {
        self.class.base
    }

    /// All fields of the class.
    ///
    /// This includes:
    /// - struct attributes annotated with `#[getter]` or `#[setter]`
    /// - methods that appear in a `#[pymethods]` block
    pub fn fields(&self) -> impl Iterator<Item = &FieldInfo<'static>> {
        self.class.fields.iter().cloned().chain(self.fields.iter().cloned())
    }
}

pub trait InspectClass {
    fn inspect() -> ClassInfo;
}

pub trait InspectStruct {
    fn inspect_struct() -> ClassStructInfo;
}

pub trait InspectImpl {
    fn inspect_impl() -> Vec<&'static FieldInfo<'static>>;
}

impl<T> InspectClass for T
where
    T: crate::PyClass,
{
    fn inspect() -> ClassInfo {
        let name = <T as PyTypeInfo>::NAME;
        let is_subclass = <T as PyClassImpl>::IS_SUBCLASS;
        let base = if is_subclass {
            Some(<<T as PyClassImpl>::BaseType as PyTypeInfo>::NAME)
        } else {
            None
        };
        let fields: Vec<&FieldInfo<'static>> = <T as PyClassImpl>::items_iter()
            .flat_map(|item| item.field_infos.iter().cloned())
            .collect();

        ClassInfo {
            class: ClassStructInfo {
                name,
                base,
                fields: vec![],
            },
            fields,
        }
    }
}

// impl<'a, T> InspectClass<'a> for T
//     where T: InspectStruct<'a>, T: InspectImpl<'a>
// {
//     fn inspect() -> ClassInfo<'a> {
//         ClassInfo {
//             class: Self::inspect_struct(),
//             fields: Self::inspect_impl(),
//         }
//     }
// }
