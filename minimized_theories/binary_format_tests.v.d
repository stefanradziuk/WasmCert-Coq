binary_format_tests.vo binary_format_tests.glob binary_format_tests.v.beautified binary_format_tests.required_vo: binary_format_tests.v ./binary_format_parser.vo ./binary_format_printer.vo ./bytes_pp.vo ./datatypes_properties.vo ./check_toks.vo ./pp.vo
binary_format_tests.vio: binary_format_tests.v ./binary_format_parser.vio ./binary_format_printer.vio ./bytes_pp.vio ./datatypes_properties.vio ./check_toks.vio ./pp.vio
