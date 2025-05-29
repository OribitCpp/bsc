add_library(
    stdcbs STATIC
    bishengc_safety/bishengc_safety.cbs
    scheduler/scheduler.cbs
    string/string.cbs
    hash/sip.cbs
    raw_table/raw_table.cbs
)

# Do not optimize, otherwise there will be missing symbols in std
target_compile_options(stdcbs PRIVATE -O0)

target_include_directories(stdcbs
    PUBLIC
    bishengc_safety
    raw_vec
    vec
    scheduler
    string
    list
    hash
    map
    option
    raw_table
    result
    rc
    cell
)

# TODO: make it work
# add_dependencies(stdcbs clang)

# install the static library
install(TARGETS stdcbs
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)

# install the header files
install(FILES
    bishengc_safety/bishengc_safety.hbs
    vec/vec.hbs
    raw_vec/raw_vec.hbs
    scheduler/queue.hbs
    scheduler/scheduler.hbs
    string/string.hbs
    list/list.hbs
    hash/sip.hbs
    map/hash_map.hbs
    option/option.hbs
    raw_table/raw_table.hbs
    result/result.hbs
    rc/rc.hbs
    cell/cell.hbs
    DESTINATION include/libcbs
)
