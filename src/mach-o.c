#include "mach-o.h"

#include <mach-o/loader.h>
#include <mach/machine.h>

void
package()
{
  struct mach_header_64 header = {};
  header.magic = MH_MAGIC_64;
  header.cputype = CPU_TYPE_X86_64;
  header.cpusubtype = CPU_SUBTYPE_ANY;
  header.filetype = MH_EXECUTE;
}
