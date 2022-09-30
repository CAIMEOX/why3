Compilation of WhyML modules into Java classes
----------------------------------------------

The ``java`` extraction driver is used to compile WhyML files into Java classes. The driver does not support `flat` extraction; thus, option ``--modular`` is mandatory. Each (non empty) module `M` is translated into a class with the same name. The imported modules are not translated unless the option ``--recursive`` is used. Since the extraction of a module requires informations related to its dependencies, the option ``--recursive`` should be used systematically. 

