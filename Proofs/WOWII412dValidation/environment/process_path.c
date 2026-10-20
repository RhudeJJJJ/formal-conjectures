#define _GNU_SOURCE
#include <dlfcn.h>
#include <unistd.h>
#include <errno.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>
static int own_pid_exe(const char *p) {
  if (strncmp(p,"/proc/",6)) return 0;
  const char *q=p+6; char *end;
  long n=strtol(q,&end,10);
  return end!=q && n==(long)getpid() && !strcmp(end,"/exe");
}
ssize_t readlink(const char *p,char *b,size_t n) {
  static ssize_t (*real_readlink)(const char *,char *,size_t);
  if (!real_readlink) real_readlink=dlsym(RTLD_NEXT,"readlink");
  ssize_t r=real_readlink(p,b,n);
  if (r<0 && own_pid_exe(p)) return real_readlink("/proc/self/exe",b,n);
  return r;
}
