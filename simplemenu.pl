use lib qw( /oraback1/tmp/testonly );
use tssml;

my ($debug_mode,$verbose_mode,$debug_mode2,$running_mode,$cmdline,$template,$target,$parafile,$cwd,$templ);

my ($cmd,$sql,$output,$sqlplus);

foreach (@ARGV) { $cmdline.="$_ "};

##########################
# step 1, parsing arguments 
##########################
if ($num_args==0){
    $running_mode=0; # non-interactive
}elsif ($cmdline =~ /(help|\-h|\-\-help)/){ # printing help information
    print "Usage as below:\n";
    print "  To run in interactive mode : perl menusetup.pl\n"; 
    print "  To run in non-interactive mode : perl menusetup.pl from=<template_name> to=<target directory> par=<parametr file>\n";
    exit 0;    
}elsif ($num_args>=3 && $cmdline =~ /from\s*\=\s*\S+\s*/ && $cmdline =~ /to\s*\=\s*\S+\s*/ && $cmdline=~ /par\s*\=\s*\S+\s*/){
    $running_mode=1; # non-interactive
    if ($cmdline =~ /(^|\s+)from\s*\=\s*(\S+)\s*/){
        $template=$2;
    }
    if ($cmdline =~ /(^|\s+)to\s*\=\s*(\S+)\s*/){
        $target=$2;
    }
    if ($cmdline =~ /(^|\s+)par\s*\=\s*(\S+)\s*/){
        $parafile=$2;
    }
    
}else{
    $running_mode=0; # interactive
}

if ($cmdline =~ /(\-\-debug\=y|\-\-debug(\s|$))/){ # printing help information
    $debug_mode=1;
    tssml::set_debug_flag('--debug');
}else{
    $debug_mode=0;
}
if ($cmdline =~ /(\-\-verbose\=y|\-\-verbose(\s|$))/){ # printing help information
    $verbose_mode=1;
    tssml::set_debug_flag('--verbose');
}else{
    $verbose_mode=0;
}
if ($cmdline =~ /\-\-debug2/){ # printing help information
    $debug_mode2=1;
    tssml::set_debug_flag('--debug2');
}else{
    $debug_mode2=0;
}

if ($cmdline =~ /\-\-debug3/){ # printing help information
    $debug_mode2=1;
    tssml::set_debug_flag('--debug3');
}else{
    $debug_mode2=0;
}

if ($running_mode && $template && $target) { # for sure it is non-interactive mode 
    print "command line is $cmdline\n";
    print "running_mode is $running_mode\n";
    print "template is $template\n";
    print "target directory is $target\n";
    print "current working directory is $cwd\n";
    print "script directory is $dirname\n";
    tssml::start_noninteractive();
}else{
    # run interactively 
    tssml::start_interactive();
}



sub get_customized_values{
 print "hello, I am in main!!!\n";
 
 
 
}
