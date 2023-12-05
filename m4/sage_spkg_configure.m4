# SYNOPSIS
#
#   SAGE_SPKG_CONFIGURE(PACKAGE-NAME,[CHECK],[REQUIRED-CHECK],[PRE],[POST])
#   SAGE_SPKG_CONFIGURE_BASE(PACKAGE-NAME,[CHECK],[REQUIRED-CHECK],[PRE],[POST],[DEPS])
#
# DESCRIPTION
#
#   This macro should be used in the build/<spkg>/spkg-configure.m4 templates 
#   for each SPKG (if defined) to specify how to check whether or not it is
#   required to be installed, and whether or not it's already installed.
#
#   The macro takes five arguments.  The first, PACKAGE-NAME, is simply the
#   base name of the SPKG.  The first two arguments, both optional,
#   implement two different kinds of checks (the first of which is more
#   common).
#
#   The next argument (which is less commonly needed) is an optional list of
#   initialization instructions which should be performed by the configure
#   script regardless whether or not the SPKG should be installed (e.g. setting
#   up --with and --enable flags).  The last argument is again commands that
#   are always run, but after the checks are performed (or if they are not
#   performed):
#
#   - CHECK - this should implement a test for whether the package is already
#     available on the system and/or meets any feature tests required for
#     Sage.  If this test fails it sets the shell variable
#     sage_spkg_install_<packagename> to "yes".  Otherwise it defaults to "no",
#     i.e., SageMath may not need to install the package.
#
#   - REQUIRED-CHECK - this checks whether or not the package is a required
#     dependency of Sage at all, depending typically on the platform.  Some
#     packages (e.g. sqlite) are only dependencies in some circumstances
#     and otherwise do not need to be checked for at all.  If
#     a REQUIRED-CHECK determines that the package is not required it sets
#     sage_require_<packagename>="no".
#
#   - PRE - always perform these actions even if the SPKG is already installed
#
#   - POST - always pwerform these actions regardless whether the SPKG will
#     be installed.
#
#   - DEPS - to pass dependencies generated by SAGE_SPKG_CONFIGURE_BASE
#
AC_DEFUN([SAGE_SPKG_CONFIGURE_BASE], [
AC_DEFUN_ONCE([SAGE_SPKG_CONFIGURE_]m4_toupper($1), [
dnl The name of this SPKG
m4_pushdef([SPKG_NAME], [$1])
dnl Whether SageMath needs to install this package
m4_pushdef([SPKG_INSTALL], [sage_spkg_install_]SPKG_NAME)
dnl Whether SageMath requires this package to be present somehow
m4_pushdef([SPKG_REQUIRE], [sage_require_]SPKG_NAME)
dnl Whether we want the system to provide this package:
dnl * "yes", attempt to use the system package
dnl * "no", do not attempt to use the system package
dnl * "force", use the system package and fail if it was deemed not suitable
dnl * other values mean that we do not want to use the system package but
dnl   indicate why
m4_pushdef([SPKG_USE_SYSTEM], [sage_use_system_]SPKG_NAME)
# BEGIN SAGE_SPKG_CONFIGURE_]m4_toupper($1)[

dnl Hide the output from Python (system site package) checks
dnl when --enable-system-site-packages was not given. This
dnl doesn't affect the test results but it minimizes the noise
dnl in the ./configure output. The config.log however retains
dnl everything.
dnl
dnl Open descriptor 9 as a copy of AS_MESSAGE_FD, so that it
dnl can later be used to restore AS_MESSAGE_FD. Afterwards,
dnl send AS_MESSAGE_FD to /dev/null. We'll restore it if this
dnl isn't a python package or if --enable-system-site-packages
dnl was given (or at the end of this macro, if nothing else).
exec 9<&AS_MESSAGE_FD
exec AS_MESSAGE_FD>/dev/null

AS_IF([test "${enable_system_site_packages}" = "yes"], [
  dnl Python package checks are enabled, so restore AS_MESSAGE_FD
  exec AS_MESSAGE_FD<&9
])

SPKG_CONFIGURE="${SAGE_ROOT}/build/pkgs/$1/spkg-configure.m4"
AS_IF([! grep -q [SAGE_PYTHON_PACKAGE_CHECK] "${SPKG_CONFIGURE}"],[
  dnl Not a python package, so restore AS_MESSAGE_FD
  exec AS_MESSAGE_FD<&9
])

echo "-----------------------------------------------------------------------------" >& AS_MESSAGE_FD
echo "Checking whether SageMath should install SPKG $1..." >& AS_MESSAGE_FD
AS_BOX([Checking whether SageMath should install SPKG $1...]) >& AS_MESSAGE_LOG_FD

AC_ARG_WITH([system-]SPKG_NAME,
       AS_HELP_STRING(--with-system-SPKG_NAME={no|yes (default)|force (exit with an error if no usable version is found)},
           [detect and use an existing system SPKG_NAME]),
       [AS_VAR_SET(SPKG_USE_SYSTEM, [$withval])]
)

AS_VAR_SET([sage_spkg_name], SPKG_NAME)

dnl Default value for most packages
AS_VAR_SET_IF([SPKG_USE_SYSTEM], [], [AS_VAR_SET([SPKG_USE_SYSTEM], [yes])])

dnl The default is not to install a package, unless a check below finds that we should.
AS_VAR_SET(SPKG_INSTALL, [no])

dnl Run DEPS
$6

dnl Run PRE
$4

dnl If a version of this package is already installed in local/ we have no
dnl choice but to use it and we will actually also update it even if it is not
dnl required.
AS_IF([test -n "`ls "${SAGE_LOCAL}/var/lib/sage/installed/${sage_spkg_name}"-* 2>/dev/null`"], [
    AC_MSG_NOTICE(m4_normalize(SPKG_NAME[ has already been installed by SageMath]))
    AS_VAR_SET(SPKG_INSTALL, [yes])
    AS_VAR_SET(SPKG_USE_SYSTEM, [installed])
])

dnl Perform REQUIRED-CHECK if present.
AS_VAR_SET_IF(SPKG_REQUIRE, [], [AS_VAR_SET(SPKG_REQUIRE, [yes])])
$3

AS_VAR_IF(SPKG_INSTALL, [no], [
    AS_VAR_IF(SPKG_REQUIRE, [no], [
        AC_MSG_NOTICE(m4_normalize([SPKG ]SPKG_NAME[ is not required on this system]))
    ], [
        dnl If this is a required package and nothing before has found that we
        dnl should install the SPKG, we run the checks to determine whether we
        dnl can use a system package.
        AS_VAR_IF(SPKG_USE_SYSTEM, [no], [
            dnl We were asked not to use the system package, so no checks are needed
            AS_VAR_SET(SPKG_INSTALL, [yes])
        ], [
            m4_ifval([$2], [
                dnl If there is a CHECK, run it to determine whether the system package is suitable
                $2
                AS_VAR_IF(SPKG_INSTALL, [no], [
                    dnl Since force did not make a difference, no need to report that force was used
                    AS_VAR_SET(SPKG_USE_SYSTEM, [yes])
                    AC_MSG_NOTICE(m4_normalize([will use system package and not install SPKG ]SPKG_NAME))
                ], [
                    AS_VAR_IF(SPKG_USE_SYSTEM, [force], [
                        AS_VAR_APPEND([SAGE_SPKG_ERRORS], ["
    Given --with-system-]SPKG_NAME[=force, but no system package could be used.
    That's an error.  Please install the indicated package to continue.
    (To override this error, use ./configure --without-system-]SPKG_NAME[)"])
                    ], [
                        AC_MSG_NOTICE(m4_normalize([no suitable system package found for SPKG ]SPKG_NAME))
                    ])
                ])
            ], [
                dnl If there is no CHECK, install the SPKG unless forced not to
                AS_VAR_IF(SPKG_USE_SYSTEM, [force], [
                    AC_MSG_NOTICE(m4_normalize([will use system package and not install SPKG ]SPKG_NAME))
                    AS_VAR_SET(SPKG_INSTALL, [no])
                ], [
                    AC_MSG_NOTICE(m4_normalize([no suitable system package found for SPKG ]SPKG_NAME))
                    AS_VAR_SET(SPKG_INSTALL, [yes])
                ])
            ])
        ])
    ])
])

dnl Run POST
$5

dnl Restore the message file descriptor that we clobbered earlier
dnl for the sake of hiding site package check noise. It's possible
dnl that we've already done this above, but it doesn't hurt to do
dnl it again, and we want everything "back to normal" at the end
dnl of this macro.
exec AS_MESSAGE_FD<&9

# END SAGE_SPKG_CONFIGURE_]m4_toupper($1)[
m4_popdef([SPKG_USE_SYSTEM])
m4_popdef([SPKG_REQUIRE])
m4_popdef([SPKG_INSTALL])
m4_popdef([SPKG_NAME])
])
])
AC_DEFUN([SAGE_SPKG_CONFIGURE], [
    SAGE_SPKG_CONFIGURE_BASE([$1], [$2], [$3], [$4], [$5], [AC_REQUIRE([SAGE_SPKG_CONFIGURE_GCC])])
])

# SYNOPSIS
#
#   SAGE_SPKG_DEPCHECK(PACKAGE-DEPENDENCIES, FURTHER-CHECK, [DEPS_ARE_INSTALLED= [sage_spkg_install_]SPKG_NAME=yes])
#                                 $1              $2                $3
#
# DESCRIPTION
#     *** to be called from SAGE_SPKG_CONFIGURE* ***
#     check for space-separated list of package dependencies $1 of package SPKG_NAME
#     do $2 if successful
#
#     $3 is for off-label use - checking a reverse dependency, by REVDEPCHECK. Then the default action of
#     setting sage_spkg_install_SPKG_NAME=yes whenever anything from $1 comes from Sage may be overwritten,
#     typically to [ ], i.e. a no-op (it can't be [], as m4_default checks non-emptiness)
#
AC_DEFUN([SAGE_SPKG_DEPCHECK], [
    m4_foreach_w([DEP], $1, [
       AC_REQUIRE([SAGE_SPKG_CONFIGURE_]m4_toupper(DEP))])
    AC_MSG_CHECKING([whether any of $1 is installed as or will be installed as SPKG])
    AS_IF([test x = y m4_foreach_w([DEP], $1, [ -o [x$sage_spkg_install_]DEP = xyes])], [
        AC_MSG_RESULT([yes; install SPKG_NAME as well])
        m4_default([$3], [sage_spkg_install_]SPKG_NAME=yes)
	], [
        AC_MSG_RESULT([no])
        $2
        ])
])


# SYNOPSIS
#
#   SAGE_SPKG_REVDEPCHECK(PACKAGE-REVERSE-DEPENDENCIES)
#                                 $1
# DESCRIPTION
#     *** to be called from REQUIRED-CHECK section of SAGE_SPKG_CONFIGURE* ***
#     check for space-separated list of package reverse dependencies $1 of package SPKG_NAME
#     If they all come from the system, do not require SPKG_NAME (i.e. it's not needed)
#
AC_DEFUN([SAGE_SPKG_REVDEPCHECK], [
    SAGE_SPKG_DEPCHECK($1, [[sage_require_]SPKG_NAME=no], [ ])
])
