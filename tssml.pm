#********************************************************************************************************************************** 
# Package Name: tssml - Template Substitution Script Marker Language   
#        Usage: It is to implement TSSML in processing text template files 
#         Note: 
#      Version: 1.2 -- Feb, 11, 2021 
#       update: 1.2.1 -- May 2, 2021
#      Author : Guangyu Yang 
# supporting tssml features:
#    <<<substitution variable>>>,  ###variable###, {{{function}}}, 
#    {{{sub}}}, -- user defined sub routine 
#    {{{class}}}, {{{obj.method}}}, {{{super.method}}} -- OO: attribute, method, override and inherit
#    {{{define}}} -- literal, array, hash and class 
#    {{{set}}}, -- literal and class attrbutes 
#    {{{foreach}}} -- looping hash and array 
#    {{{while}}}, {{{case}}}, {{{case when}}},{{{hash_keys}}},{{{fi_writefile}}}
#    {{{fo_chmod}}} -- change file permission after it is generated
#    <<<<hash:>>> --- hash loading directives
#    additional_params_file -- parameter file for substitution variables with name, small description and default values 
#                 --- add:  list(....) as predefined list for additional parameters <--- to be added 
# supporting tssml functions :
#     1. define : declare stack variable 
#     2. skip   : do nothing and return nothing 
#     3. thru   : do nothing and return original input 
#     4. mute   : tell intepretor, it's the better not prompt for value of the substitution variable 
#     5. ref    : link a stack variable to a substitution variable
#     6. set    : assign value to stack variable or class object attribute 
#     7. push_hash : push value to hashtable 
#     8. iif    : inline if condition 
#     9. expr   : evaluate expression 
#    10. hash_keys : get keys of a hash 
#    11. flat_list_f : convert array elements or hash keys into one line and optionally call a function to preprocess each element before merge to a list 
#    12,13,14. sub_l,sub_r, sub_m   : substring functions 
#    15,16. pad_t, pad_s  : pad string to certain length with spaces 
#    17,18. lc, uc : convert string to all lowercase or uppercase 
#    19. wrap_lst_ : 
#    20. diff_update :  compare files and only append new lines to file 
#    21. fi_writefile :  parameterize the file names to be iterated and generated respectively 
#    22. range :  create array based on range of numbers or string list 
#    23. get_args   
#    24. contains : check exisitence of array or hash elements 
#    25. fields :  get fields from a string with delimiter defined 
### notes 
#**********************************************************************************************************************************
package tssml;

use strict;
use POSIX;
use Time::Local qw( timelocal );
use File::Basename;
use File::Copy;
use Net::Domain qw(hostname hostfqdn hostdomain domainname);
use Cwd qw(cwd);
use Storable 'dclone';
use File::Spec::Functions 'catfile';

my $gtree={}; # parsing tree for each file 
my $gsets={}; # global setting 

# will move below variables into gsets 
my $num_args = $#ARGV + 1;
my ($jobname) = ($0 =~ m|.*\/(\w+\.*\w*)$|);

## use more generic interface 

# internal variables 
my $__inited=0;
my $debug_mode=0;
my $debug_mode2=0;
my $debug_mode3=0;
my $debug_mode4=0;
my $verbose_mode=0;
my $sub_depth=0;
my $__loop_lmt=1000000; # threshold for loop to avoid dead loop 
my $___prev_tl;
my $show_ref_while_walking=0;
my $hide_parent_while_walking=1;


my $additional_params_file=".___additional_template_vars_menusetup";
$gsets->{param_file}=$additional_params_file;
$gsets->{template_dir} = dirname(Cwd::abs_path($0));
$gsets->{cwd}=cwd();

################
# safe compartment to run reval 
use Safe;
my $compartment = new Safe;
$compartment->permit_only(qw (padany :base_core));
$gsets->{safe}=$compartment;
##############
## global variables in hashtable 
my $preview_banner_width=52;
my $app_params; ## variables that has values provided in anyway
my $raw_params; ## variables that has not yet provided values 
my $ref_params; ## map from stacked variable to global substitution variable <name> to <name> , not actual reference
my $muted_params={}; ## variables that are muted -- in other words, won't prompt for input 
my $sub_defs={};## definition of subroutine , this is global by default, but when parsing class, it will be rerouted to cls_defs   
my $arr_refs={};## array reference box<<<< to be removed 
my $cls_defs={};## class definition, global 
####################################################
# internal subroutines  
sub __init_settings{
    __get_hostname();
    $__inited=1;
}
sub __get_hostname{
    my $p="$^O\n";
    $gsets->{os_type}=$p;
    $p=hostfqdn();
    chomp($p);
    $gsets->{hqdn}=$p;
}
sub __init_gtree{
    my $ola=@_[0];
    my $onum=scalar @{$ola};
    my @nl=();
    $gtree={};
    $gtree->{current_level}=0;
    $gtree->{current_line}=0;
    $gtree->{current_node}=0;
    $gtree->{source}=$ola;
    $gtree->{total_lines}=$onum;
    $gtree->{nlines}=\@nl; # to save result lines    
    $gtree->{status}=0; #0=idle 
    $gtree->{type}='root'; # root tree
}
sub set_debug_flag{
    my $cl=$_[0];
    $debug_mode=1 if ($cl =~ /(\-\-debug\=y|\-\-debug(\s|$))/); # printing help information
    $verbose_mode=1 if ($cl =~ /(\-\-verbose\=y|\-\-verbose(\s|$))/); # printing help information
    $debug_mode2=1 if ($cl =~ /\-\-debug2/); # printing help information
    $debug_mode3=1 if ($cl =~ /\-\-debug3/); # printing help information
    $debug_mode4=1 if ($cl =~ /\-\-debug4/); # printing help information
}

#################################################################################
# start_interactive
#   proc_id : 0010 
#   purpose : Entry point which will run whole module interactively    
# arguments : template_directory (optional)
#      pre  : if the caller script is not in the parent directory of templates, 
#                call set template_dir first to tell the package where the templates are 
#             otherwise, no mandatory preliminary steps
#     post  : optionally, inherit get_customized_values in main program 
#################################################################################
sub start_interactive{
    my $tpl_dir=$_[0];    
    __init_settings() unless($__inited);
    
    if ($tpl_dir ne '' && -e $tpl_dir){
        $gsets->{template_dir}=$tpl_dir;
    }else{
        $tpl_dir=$gsets->{template_dir};
    }

    #print "tpl_dir=$tpl_dir\n";
    
    print "current working directory is $gsets->{cwd}\n";
    print "script directory is " . $gsets->{template_dir} . "\n\n";    

    opendir DIR ,$tpl_dir;
    my @template_arr=();
    while (my $thing = readdir DIR) {
        chomp($thing);
        if ($thing ne '.' && $thing ne '..' && -d "$tpl_dir/$thing"){
            push(@template_arr,$thing);
        }
    }   
    closedir DIR;
    
    if (scalar @template_arr <= 0){
        die "*** Error ! no template exists under $tpl_dir ***\n\n"; 
    }
    
    print "Available Templates under $tpl_dir :\n";
    for my $tl (0..$#template_arr){
        print " ".($tl+1)." - ${template_arr[$tl]} \n";
    }

    print "Select Template[ ${template_arr[0]} ]:";
    my $template=<STDIN>;
    chomp($template);
    
    if ($template =~/^\s*\Z/){
        $template=${template_arr[0]};
    }

    print "*** template is $template\n";
    
    $gsets->{template_selected}=$template;
    
    print "Select Target Directory[$gsets->{cwd}]:";

    my $target=<STDIN>;
    chomp($target);

    if ($target =~/^\s*\Z/){
        $target="$gsets->{cwd}";
    }
    print "*** target directory is $target\n";
    
    $gsets->{target}=$target;
    
    if ($target eq "$tpl_dir/$template"){
        die "*** Error *** You are going to write files to template directory!\n That would destory template, you must change to different target directory.\n";
    }   
    __parse_template($template); 
    
    print "Getting values for substitution variables detected in template...\n";
    
    get_customized_values();  
    __get_variable_values();
    __print_preview();
}
#################################################################################
# get_customized_values
#   proc_id : 0020 
#   purpose : define this subroutine with exact same name to inherit it.    
# arguments : none
#      pre  : ___parse_template is called so that all substitution variables are detected 
#     post  : optionally, inherit get_customized_values in main program 
#     note  : do not modify this subroutine 
#################################################################################
sub get_customized_values{
    #print "hello!!! this is get_customized_values in package\n";
    # caller can inherit this sub to enhance the parameter 
    main::get_customized_values() if (defined &main::get_customized_values); 
}
#########################################################################################################
# __parse_template
#   purpose : parse template to get all substitution variable names required in the templates   
#   proc_id : 0030
# arguments : template name
#      pre  : this is internal routine , getparams_interactive or getparams_noninteractive calls this sub 
#     post  : call get_customized_values
#     note  : Not needed to be called in your code 
#########################################################################################################
sub __parse_template{
    my $template=$_[0];
    my $dirname=$gsets->{template_dir};
    my $tl=catfile($dirname,$template);
    print "Parsing template ...\n";    
    opendir DIR ,$tl;
    my @files=readdir(DIR);
    close DIR;
    my $j=0;
    foreach my $ttl (@files){
        next if ($ttl eq '.' || $ttl eq '..');
        $j++;
        if ($ttl eq $additional_params_file){
            print "Found additional parameter definition file: $ttl in template\n";
            print "Extracting additional parameter definition...\n";
            parse_params_def_file(catfile($tl,$ttl));
            next;
        }
        
        print "Looking for variables in file $ttl content\n" if ($debug_mode || $debug_mode2);
        open(FS, '<', catfile($tl,$ttl)) or die $!;
        chomp(my @lines = <FS>);
        foreach my $fl (@lines){
            __parse_template_line($fl);
            if ($fl =~/^\s*\{\{\{mute\s+(.+)\s*\}\}\}$/){
                my @ll=split(/\s+/,$1);
                print "Muting input for @ll\n" if ($debug_mode);
                foreach my $llr (@ll){
                    $muted_params->{$llr}->{muted}='y';
                }
            }
        }
        close FS;
    }    
    die "**** Error ! Empty template, nothing to process\n" if ($j<=0);
    if ($verbose_mode || $debug_mode){
        print "Detected below variables...\n";
        __print_params('raw');
    }
}
#########################################################################################################
# __parse_params_def_file
#   purpose : extract substitution variables from default parameter file    
#   proc_id : 0031
# arguments : default parameter file name
#      pre  : none
#     post  : none
#     note  : Not needed to be called in your code 
#########################################################################################################
sub parse_params_def_file{
    my $ttl=$_[0];
    open(FS, '<', "$ttl") or die $!;
    chomp(my @lines = <FS>);
    my $delim='\s+';
    my @arr;
    foreach my $fl(@lines){
        next if ($fl=~/^\s*#/); #skip, it is comment line 
        if ($fl=~/^\s*\!\s*(\w+)\s*(.*)$/){ # command line in parameter file 
            my $cmd=$1;
            my $drc=$2;
            if ($cmd eq 'delim'){ # delimiter command 
                if ($drc=~/^\s*(\S+)(\s*|$)/){
                    $delim=$1;
                }
            }    
            next;
        }
        print "delimiter is set to $delim\n" if ($debug_mode);
        @arr=split($delim,$fl);
        if (defined $arr[0] && length($arr[0])>0){
            $arr[0]=~s/(^\s+|\s+$)//g;
            print "adding @arr to raw_params \n" if ($debug_mode);
            $raw_params->{$arr[0]}->{name}=$arr[0];
            $raw_params->{$arr[0]}->{type}=$arr[1] if (defined $arr[1]);
            if (defined $arr[2]) {
                $arr[2]=~s/(^\s+|\s+$)//g;
                $raw_params->{$arr[0]}->{default}=$arr[2];
            }
            $raw_params->{$arr[0]}->{desc}=$arr[3] if (defined $arr[3]);
        }
        
    }
}
#########################################################################################################
# __parse_template_line
#   purpose : parse each line of template file to find all substitution variables    
#   proc_id : 0040
# arguments : original line read from template file 
#      pre  : this is internal routine , parse_template sub calls this sub 
#     post  : none
#     note  : Not needed to be called in your code
#########################################################################################################
sub __parse_template_line{
    my $ta=@_[0];
    return if ($ta=~/^\s*$/);
    print "parsing string: $ta\n" if ($debug_mode);
    # this step can only detect fixed variable name
    # if variable name is dynamic, it can only be detected when process_template is called 
    if ($ta =~ /(.*)<<<(((?!<<<).|(?!>>>).)+)>>>(.*)/){
        print "matched 1=$1 , 2=$2, 3=$3, 4=$4, 5=$5, 6=$6 ,7=$7\n" if ($debug_mode);
        my ($h,$t,$c);
        $h=$1;
        $t=$4;
        $c=$2;
        if ($c=~/^\s*(\w+)\s*$/){
            $c=$1;
            if ($debug_mode || $verbose_mode){
                if (defined $raw_params->{$c} && defined $raw_params->{$c}->{name}){
                    print "$c is already found. Skip.\n";                
                }else{
                    print "Found variable name=$c, save to hashtable.\n";
                }
            }
            $raw_params->{$c}->{name}=$c;
        }elsif ($c=~/^\!(\w+.+)\s+(\w+)\s*$/){
            my $cmdd=$1;
            my $varr=$2;
                print("Found command $cmdd for substitution variable $varr\n") if $debug_mode;
                $raw_params->{$varr}->{name}=$varr;
                $raw_params->{$varr}->{command}=$cmdd;
                $raw_params->{$varr}->{type}='hash';
        }else{
            print "$c is not a proper variable name. Skip.\n" if ($debug_mode2); 
        }        
        __parse_template_line($h) if ($h!~/^\s*$/);;
        __parse_template_line($t) if ($t!~/^\s*$/);
    }
}
########################################################################################
# get_variable_values 
#  proc_id : 0050
#  purpose : 1. prompt user for each substitution variable values by the name detected in template files   
#  pre     : parse_template sub is called
#  post    : print_preview or process_template will be called 
########################################################################################
sub __get_variable_values{
    my ($name,$type,$default,$desc,$cmdd,$templ);
    foreach my $k (sort keys %{$raw_params}){
        if ($app_params->{$k} !~ /\S+/){
            $name=$raw_params->{$k}->{name};
            $type=$raw_params->{$k}->{type};
            $default=$raw_params->{$k}->{default};
            $desc=$raw_params->{$k}->{desc};
            $cmdd=$raw_params->{$k}->{command};
            
            print "$k needs value\n" if ($debug_mode || $debug_mode2);
            print "\n------------------------------------------------------------------\n";
            if ($desc !~/^\s*$/){
                print "$desc";
                print "\n------------------------------------------------------------------\n";
            }
            print "$k has no value provided but is required in template\n";
            if (defined $cmdd){
                my $rett=__get_variable_values_with_command($raw_params->{$k});
                next if ($rett);
            }
            if ($type =~ 'list\((.*)\)'){
                my $templ=$1;
                my @tmp_arr=split(/,/,$templ);
                my $ii=1;
                foreach my $templ (@tmp_arr){
                    chomp($templ);
                    print " $ii. $templ\n";
                    $ii++;
                }
                print " Pick one from the list or provide your own value otherwise will use the default value.\n Provide value for $k [ $default ]:";  
            }else{
                print " For multiple values, use ',' as delimiter.\n Put nothing if you want to skip.\n Now, provide value for $k [ $default ]:";
            }
            $templ=<STDIN>;
            chomp($templ);
            $templ =~ s/^\s+|\s+$//g;
            
            if ($templ =~ /\S+\,/){
                print "The input is a list, convert to array\n" if ($debug_mode || $debug_mode2);
                my @tmp_arr=split(/,/,$templ);
                $app_params->{$k}=\@tmp_arr;
                print "\n*** $k *** is set to $templ\n\n";            
            }elsif ($templ !~/^\s*\Z/){
                $app_params->{$k}=$templ;
                print "\n*** $k *** is set to $templ\n\n";
            }else{
                if ($default =~ /\S+\,/){
                    my @tmp_arr1=split(/,/,$templ);
                    $app_params->{$k}=\@tmp_arr1;
                    print "\n*** $k *** is set to defalt value in array: @tmp_arr1\n\n";
                }else{
                    $app_params->{$k}=$default;                
                    print "\n*** $k *** is set to defalt value : $default\n\n";
                }
            }
        }
    }    
    print "\n";
}
#########################################################################################################
# __get_variable_values_with_command
#  proc_id : 0051
#  purpose : parse substitution variable with directives    
#  pre     : parse_template sub is called
#  post    : print_preview or process_template will be called 
########################################################################################
sub __get_variable_values_with_command{
    my $v=$_[0];
    return if ! defined $v;
    my ($name,$type,$default,$desc,$cmdd,$templ);
    $name=$v->{name};
    $type=$v->{type};
    $default=$v->{default};
    $desc=$v->{desc};
    $cmdd=$v->{command};
    
    my (@arr1,@arr2);
    
    if ($cmdd=~/^\s*hash(.*)\s*$/){
        $cmdd=$1;
        print("The substitution variable is requiring you to follow directives to build a Hashtable.\n") if $debug_mode;
        my $stage_hash;
        if ($cmdd=~/\((.+)\)/){
            $cmdd=$1;
            @arr1=split_q(",",$cmdd,1);
            print("Parsing Hashtable Building Directives... ...\n".join('<-->',@arr1)."\n") if $debug_mode;
            $stage_hash={};
            foreach my $akk (@arr1){
                @arr2=split_q(":",$akk,1);
                print("akk=$akk, after split is @arr2[0] and @arr2[1]\n") if $debug_mode;
                my $work_hash=$stage_hash;
                if (@arr2[0]=~/^(.+)(\+|\-)$/){
                    my $kky=$1;
                    my $flg=$2;
                    my @arr3=split('\.' ,$kky);
                    print("----> kky=".$kky) if $debug_mode;
                    print("----> flg=".$flg) if $debug_mode;
                    print("----arr3=(".join(",",@arr3).")\n") if $debug_mode;
                    my $l_a3=scalar @arr3;
                    my $ll=0; 
                    foreach my $pkk (@arr3){
                        $work_hash->{$pkk}={} if ! defined($work_hash->{$pkk});
                        $work_hash=$work_hash->{$pkk};
                        print("ll=$ll, l_a3=$l_a3\n") if $debug_mode;
                        if ($ll==($l_a3-1)){
                            $work_hash->{flag}=$flg;
                            $work_hash->{cmd}=@arr2[1];
                            if ($flg eq '-'){
                                $work_hash->{desc}="will add a sub-key, named  @arr2[1] , to the [ $kky ]. And then ask for its value(s)";
                            }elsif ($flg eq '+'){
                                $work_hash->{desc}="will ask user to input value(s) for [ $kky ].";
                            }
                        }
                        $ll++;
                    }
                }
            }
            if ($debug_mode){        
                walk_dict($stage_hash,1,1,"Parsing the hash directives for $name ....");
            }
        }
        __traverse_staging_hash($app_params,$stage_hash,$name);
        walk_dict($app_params,1,1,"After load staging hash into parameter, $name");
        return 1;
    }
}
#########################################################################################################
# __traverse_staging_hash
#  proc_id : 0052
#  purpose : based on hash directives for substitution variable, prompt use for inputs     
#  pre     : parse_template sub is called, __get_variable_values_with_command is called 
#  post    : print_preview or process_template will be called 
########################################################################################
sub __traverse_staging_hash{
    my $target_hash=$_[0];
    my $hash=$_[1];
    my $varname=$_[2];
    my $parent_name=$_[3];
    my $templ;
    
    if ($debug_mode){
        if (defined $parent_name){
            print("Get inputs for $varname of $parent_name ...\n") ;
        }else{
            print("Get inputs for $varname...\n") ;
        }
    }
    if (! defined $target_hash->{$varname}){
        $target_hash->{$varname}={};
    }
    
    $target_hash=$target_hash->{$varname};
    
    my @children; 
    my $save_target_hash;
    
    foreach my $k (keys %$hash){
        my $v=$hash->{$k};
        if (ref $v ne 'HASH'){
            next;
        }
        my $flg=$v->{flag};
        my $cmd=$v->{cmd};
        my $desc=$v->{desc};
        my @arr1=();
        if ($flg eq '+'){ 
            if (defined $parent_name){
                print(">>>>>>>>>>>>>>>>>>>>>>>>>>\n");
                print("This is for $cmd of $parent_name :\n");
            }else{
                print(">>>>>>>>>>>>>>>>>>>>>>>>>>\n");
                print("This is for $cmd :\n");
            }
            print(" For multiple values, use ',' as delimiter. Put nothing if you want to accept the value in bracket. [ ]:\n");
            $templ=<STDIN>;
            chomp($templ);
            next if (! defined $templ || $templ=~/^\s*$/); 
            @arr1=split(",",$templ);
            foreach my $ark (@arr1){ 
                if (!defined $target_hash->{$ark}){
                    $target_hash->{$ark}={};
                }
            }
        }elsif ($flg eq '-'){
            print("adding branch $cmd to $varname\n") if $debug_mode;
            if (! defined $target_hash->{$cmd}){
                $target_hash->{$cmd}={};
            }
        }
        
        foreach my $f (keys %$v){
            if ($f !~ /^\s*(flag|cmd|desc)\s*$/){
                push(@children,$f);
            }
        }
        $save_target_hash=$target_hash;
        foreach my $child (@children){
            if ($debug_mode){
                my @temp=%$target_hash;
                print("Adding $child to @temp\n");
            }
            foreach my $arj (@arr1){
                if ($debug_mode){
                    print("arj=$arj ,key=$v->{child}->{cmd}\n");
                }
                $target_hash=$save_target_hash->{$arj};
                my $tcm=$v->{$child}->{cmd};
                if (! defined ($target_hash->{$tcm})){
                    $target_hash->{$tcm}={};
                }
                __traverse_staging_hash($target_hash,$v->{$child},$tcm,$arj);
            }
        }
    }        
}
########################################################################################
# print_preview
#  proc_id : 0060
#  purpose : print all substitution variable names and their values provided 
#            ask user whether to proceed 
#  pre     : all global variables/substitution variables have their values provided  
#            1. can be done by call set_app_variable function individually
#            2. can be done by calling get_variable_values();
#  post    : all done 
########################################################################################
sub __print_preview{
    my $template=$gsets->{template_selected};
    my $cwd=$gsets->{cwd};
    my $target=$gsets->{target};
    my $templ;
    
    my $wid=$preview_banner_width;
    my $head="+"."-"x ($wid-2) . "+";
    print "$head\n";
    print "| ".pad_s(($wid-4),"Reviewing inputs before start....")." |\n";
    print "$head\n";
    print "| ".pad_s(($wid-4),"Template name is $template")." |\n";
    print "| ".pad_s(($wid-4),"Target directory is $target")." |\n";
    print "| ".pad_s(($wid-4),"Working directory is $cwd")." |\n";
    print "$head\n";
    print "| ".pad_s(($wid-4),"All Parameter List :")." |\n";
    __print_params();
    print "\nProceed (y|n) [ n ] :";
    $templ=<STDIN>;
    print "\nYour choice is $templ\n";
    chomp($templ);
    if ($templ =~/^(y|yes)\Z/i){
        print "Proceeding...\n";
    }else{
        print "Exiting...\n";
        exit 0;
    }
    __process_template();
    
    print "Template $template execution is complete.\n";
}
########################################################################################
# process_template
#  proc_id : 0070 
#  purpose : 1. parase template files 
#            2. get values for global variables aka. substitution variables 
#            3. compute local variables, aka. stacked variable
#  pre     : all global variables/substitution variables have their values provided  
#            1. can be done by call set_app_variable function individually
#            2. can be done by calling get_variable_values();
#  post    : all done 
########################################################################################
sub __process_template{
    my $template=$gsets->{template_selected};
    my $dirname=$gsets->{template_dir};
    my $target=$gsets->{target};

    print "Template location is [ $dirname ]\n";
    print "Extracting files from template [ $template ]\n";    
    my $tl=catfile($dirname,$template);
    opendir DIR ,$tl;
    my @files=readdir(DIR);
    close DIR;
    my $ntl;
    foreach my $ttl (@files){
        next if ($ttl eq '.' || $ttl eq '..' || $ttl eq $additional_params_file);
        print "\nCopying file:[$ttl] to $target...\n" if ($debug_mode); 
        
        $sub_depth=0;   # checking file name

        if ($ttl=~/\{\{\{\s*fi_/){# has file_iterator call, multiple file operation is required.
            __file_iterator($ttl,$tl,$target);
            next; # file_iterator will deal with the target file 
        }
              
        $ntl=__substitute_string($ttl);
        print "<<< File $ttl was processed by top level function.\n" if ($debug_mode && $sub_depth<0);
        print "Complete.\n" if ($sub_depth==-1);
      
        next if ($sub_depth==-1 || $sub_depth==-2);
        
        $sub_depth=1;    # checking file content 
        open(FS, '<', catfile($tl,$ttl)) or die $!;
        print "Processing file content\n";
        chomp(my @lines = <FS>);
        close FS;

        my @nlines;
        #print "before processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
        __init_gtree(\@lines);
        __process_file_content(\@lines);
        @nlines=@{$gtree->{nlines}};# must get it back, otherwise it might be a different one
        #print "after processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);        
        print "Creating $target/$ntl\n";
        open(FH, '>', catfile($target,$ntl)) or die $!;
        foreach my $tl (@nlines){
            print FH "$tl\n";
        }
        close FH;
        print("checking file options\n") if ($debug_mode);
        implement_fo($gtree,catfile($target,$ntl));
        clear_fo($gtree);
        print "Complete.\n";

    }
}
########################################################################################
# substitute_string
#  proc_id : 0080
# argument : string contains substitution variable or plain text  
#  purpose : replace all substitution variables with their provided values in whereever the appear in the tempalte file 
#  pre     : parse_template & process_template are called 
#  post    : call __run_tester which is the actual worker routine  
########################################################################################
sub __substitute_string{
    my ($tl)=@_;
    my $final=__run_tester($tl);
    #print "final string is $final\n";
    return $final;
}
########################################################################################
# run_tester
#  proc_id : 0081
# argument : string contains substitution variable or plain text  
#  purpose : this is associated worker routine assisting substitute_string 
#  pre     : parse_template & process_template are called 
#  post    : 
########################################################################################
sub __run_tester{
    my ($tl)=@_;
    print "processing input line is $tl\n" if ($debug_mode && $verbose_mode);
    if ($tl=~/(.*){{{(((?!}}}).)*)}}}(.*)/){
        my $prev=$1;
        my $proc=$2;
        my $post=$4;
        my ($f,$p,$t);
        
        print "S1=$1, S2=$2, S4=$4\n" if ($debug_mode && $verbose_mode);
        
        if ($proc=~/^\s*(\S+)(\s+|<<<|\{\{\{|\#\#\#)(.+)\s*\Z/){
            $f=$1;
            $t=$2;
            $p=$3;
            print "f=$f, t=$t, p=$p\n" if ($debug_mode);
            $p="<<<$p" if ($t eq '<<<');
            $p="{{{$p" if ($t eq '{{{');
            print "function name is $f\n" if $debug_mode;
            $p=__run_tester($p);
            print "parameter is $p\n" if ($debug_mode);
            print "$p is a ARRAY ref, passing to __run_func $f\n" if ($debug_mode && ref $p);            
            $proc=__run_func($f,$p,$proc);
        }elsif ($proc=~/^\s*(\S+)\s*\Z/){
            $f=$1;
            print "f=$f, t=$t, p=$p\n" if ($debug_mode);
            print "function name is $f\n";
            $proc=__run_func($f,$p,$proc);
        }
        
        if ((ref $proc)=~/(HASH|ARRAY)/){
            print ("return value is a ref, stack it : $proc\n") if ($debug_mode && $verbose_mode);
            $proc=__stack_func_ref($proc);
            $proc=" ###$proc### ";
        }
        return __run_tester($prev.$proc.$post);
        
    }elsif ($tl=~/(.*)<<<(((?!>>>).)*)>>>(.*)/){
        my $prev=$1;
        my $proc=$2;
        my $post=$4;
        print "*S1=$1, S2=$2, S4=$4\n" if ($debug_mode);
        $prev=__run_tester($prev);
        $post=__run_tester($post);
        $proc=__fetch_variable($proc);
        print "*prev=$prev, proc=$proc, post=$post\n" if ($debug_mode);
        
        my $typ=ref $proc;
        if ($typ=~/(ARRAY|HASH)/){
            print "It is array/hash ref, saving to stack_func_refs\n" if ($debug_mode);
            $proc=__stack_func_ref($proc);
            print "returned $proc\n" if ($debug_mode);
            $proc=" ###$proc### ";
            $arr_refs->{"$proc"}=$proc;
        }
        #return $proc if (ref $proc eq 'ARRAY'); # do not process ARRAY ref, return it directly , head & tail will be abandoned 
        return $prev.$proc.$post;
        
    }elsif ($tl=~/^([^\"]*)\"([^\"]+)\"(.*)/){
        my $prev=$1;
        my $post=$3;
        my $proc=$2;
        
        #print "found enclosed string S1=$prev, S2=\"$proc\", S3=$post\n" if ($debug_mode);
        $prev=__run_tester($prev);
        $post=__run_tester($post);
        #print "Returning string $prev\"$proc\"$post\n" if ($debug_mode);
        
        return "$prev\"$proc\"$post";    
    }else{
        return $tl;
    }
}
########################################################################################
# file_iterator
#  proc_id : 0090
# argument : filename_command, source_dir, target_dir   
#  purpose : filter iterator is a utility to generate multiple files based on the fi commands  
#  pre     : parse_template & get_variable_values are called.  
#  post    : based on the criteria provided in the filename_command, multiple files are to be created   
########################################################################################
sub __file_iterator{
    my $filename=$_[0];
    my $sdir=$_[1];
    my $tdir=$_[2];
    print "file_iterator is called, filename=$filename, source=$sdir, target=$tdir \n"  if ($debug_mode);
    # you need to find the exact match of the function and its paramater 
    
    if ($filename =~ /(((?!{{{fi_).)*)\{\{\{\s*fi_(\w+)(\s+)(.+)$/){
        # found file iterator function 
        my $fn= $3;
        my $h = $1;
        my $t = $5;
        print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7 file_iterator\n" if ($debug_mode); 
        ###################
        # gen2 sub routine 
        if ($fn eq 'gen2'){ #interation of parent-child hash/array
            my $pos=__find_match('{{{','}}}',$t); # find body of fi_gen2 function 
            my $body = substr($t,0,$pos);
            print ">>>>>  find pos=$pos body=$body\n" if ($debug_mode);
            if ($body=~/\s*(\w+)\s+in\s+(.+)$/){
                my $var1=$1;
                my $r=$2;
                print "var1=$var1, r=$r\n" if ($debug_mode && $verbose_mode);
                my @posd=__find_first_collection($r);
                print ">>>>> First Collection Detection : posd=". join(',',@posd)."\n" if ($debug_mode);
    
                my $body2=$posd[3];
                my $var2;
                if ($body2=~/\s*(\w+)\s+in\s+(.+)/){
                    $var2=$1;
                    $r=$2;
                }else{
                    print "Syntax Error while parsing gi_gen2 function : $body2\n";
                    return;
                }
    
                print "var2=$var2, r=$r\n" if ($debug_mode && $verbose_mode);
    
                my $typ=$posd[1];
                my @arr1;
                if ($typ eq 's'){
                    my $col=$app_params->{$posd[2]};
                    $typ=ref $col;
                    if ($typ eq 'HASH'){
                        @arr1=keys %$col;
                    }
                }
                
                my @posd2=__find_first_collection($r);
                print ">>>>> First Collection Detection : posd2=". join(',',@posd2)."\n" if ($debug_mode);

                if ($posd2[2] =~ /^\s*hash_keys/){
                    my $oldv=$gtree->{stack}->{$var1};
                    my $gi_param=$posd2[3];
                    foreach my $tii (@arr1){
                        $gtree->{stack}->{$var1}=$tii;
                        my $hd=__run_func('hash_keys',substr($posd2[2],$posd2[0]+9));
                        my @result;
                        if (ref $hd){
                            @result=keys %$hd;
                        }else{
                            @result=($hd);
                        }
                        print "result is ". join(',',@result)."\n" if ($debug_mode && $verbose_mode);
                        my $oldvj=$gtree->{stack}->{$var2};
                        foreach my $tjj(@result){
                            $gtree->{stack}->{$var2}=$tjj;
                            my $argline=__translate_stacked_vars($gi_param);
                            $argline=__substitute_string($argline);
                            print "going to gen files with $argline\n" if ($debug_mode && $verbose_mode);
                            my $gi_fname;
                            my $gi_args;
                            if ($argline=~/fi_name\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)/){
                                print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7 fi_name\n" if ($debug_mode && $verbose_mode); 
                                $gi_fname=$1;
                                $gi_args=$5;
                                $gi_fname=~ s/\s+$//;
                                if ($gi_args eq 'fi_args'){
                                    if ($argline=~/fi_args\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)/){
                                        print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7 fi_args\n" if ($debug_mode && $verbose_mode); 
                                        $gi_args=$1;
                                    }
                                }
                                #print "Going to create file $tdir/$gi_fname with args $gi_args \n";
                                __run_func('fi_writefile',"source=$filename;target=$tdir/$gi_fname;args=$gi_args");
                            }else{
                                print "Failed to get filename from $argline\n";
                            }
                        }                            
                        if (defined $oldvj){
                            $gtree->{stack}->{$var2}=$oldvj;
                        }else{
                            undef $gtree->{stack}->{$var2};
                        }                            
                    }
                    if (defined $oldv){
                        $gtree->{stack}->{$var1}=$oldv;
                    }else{
                        undef $gtree->{stack}->{$var1};
                    }
                }
            }else{
                print "Syntax wrong:$body\n  should be \"\{\{\{fi_gen2 var in collection1 collection2 \}\}\}\"";
            }
        ###################
        # gen1 sub routine 
        }elsif ($fn eq 'gen1'){ #interation of a hash/array
            my $pos=__find_match('{{{','}}}',$t); # find body of fi_gen2 function 
            my $body = substr($t,0,$pos);
            print ">>>>>  find pos=$pos body=$body\n" if ($debug_mode);
            if ($body=~/^\s*(\w+)\s+in\s+(.+)$/){
                my $var1=$1;
                my $set=$2;
                my $arglist_orig;
                
                my @posd2=__find_first_collection($set);
                print ">>>>> First Collection Detection : posd2=". join(',',@posd2)."\n" if ($debug_mode);
                
                if ($posd2[1] eq 'h'){
                    
                }elsif ($posd2[1] eq 's'){
                    $set="<<<".$posd2[2].">>>";
                    $arglist_orig=$posd2[3];
                }
                
                print "var1=$var1, set=$set, arglist_orig=$arglist_orig\n" if ($debug_mode && $verbose_mode);
                $set= __substitute_string($set);
                $set=__translate_stacked_vars($set);
                $set=__fetch_stacked_vars($set);                
                print "set=$set\n";
                my $oldvj=$gtree->{stack}->{$var1};
                my @result;
                if (ref $set eq 'HASH'){
                    @result=keys %$set;
                }elsif (ref $set eq 'ARRAY'){
                    @result=@$set;
                }else{
                    @result=[$set];
                }
               
                foreach my $tjj(@result){
                    $gtree->{stack}->{$var1}=$tjj;
                    my $argline=$arglist_orig; 
                    $argline=__substitute_string($argline);
                    $argline=__translate_stacked_vars($argline);
                    print "going to gen files with $argline\n" if ($debug_mode && $verbose_mode);
                    my $gi_fname;
                    my $gi_args;
                    if ($argline=~/fi_name\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)/){
                        print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7 fi_name\n" if ($debug_mode && $verbose_mode); 
                        $gi_fname=$1;
                        $gi_args=$5;
                        $gi_fname=~ s/\s+$//;
                        if ($gi_args eq 'fi_args'){
                            if ($argline=~/fi_args\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)/){
                                print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7 fi_args\n" if ($debug_mode && $verbose_mode); 
                                $gi_args=$1;
                            }
                        }
                        #print "Going to create file $tdir/$gi_fname with args $gi_args \n";
                        __run_func('fi_writefile',"source=$filename;target=$tdir/$gi_fname;args=$gi_args");
                    }else{
                        print "Failed to get filename from $argline\n";
                    }
                }                            
                if (defined $oldvj){
                    $gtree->{stack}->{$var1}=$oldvj;
                }else{
                    undef $gtree->{stack}->{$var1};
                }                            
            }        
        ###################
        # genx sub routine, can handle endless nested hash/arrays , will replace gen1 and gen2 later  
        }elsif ($fn eq 'genx'){ #interation of a hash/array
            my $ph={};
            $ph->{str}=$filename;
            $ph->{type}='r';
            $ph->{nodeidx}=0;
            $ph->{status}='idle';
            my @arr=__find_nested_pairs('{{{','}}}',$ph);
            walk_dict($ph,1,1,"Test Only");
        }
    }
}
########################################################################################
# implement_fo
#  proc_id : 0091
#  purpose : called by implement_fo as worker subroutine to set file permission  
########################################################################################
sub implement_fo{
    my $vt=$_[0];
    my $fh=$_[1];
    if (defined $vt && defined $fh){
        my $oh=$vt->{file_options};
        return if !defined $oh;
        foreach my $k (keys %$oh){
            if ($k eq 'chmod'){
                my $v=$oh->{chmod};
                if ($v=~/^\s*\d+\s*$/){
                    chmod oct($v),$fh;
                }
            }
        }
    }
}
########################################################################################
# implement_fo
#  proc_id : 0092
#  purpose : called by implement_fo as worker subroutine to set file permission  
########################################################################################
sub clear_fo{
    my $vt=$_[0];
    undef $vt->{file_options} if (defined $vt);
}

########################################################################################
# process_file_content
#  proc_id : 0100
# argument : none   
#  purpose : process file content before write to target directory   
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited 
#  post    : 
########################################################################################
sub __process_file_content{
    __explore_file();
    if ($debug_mode2){
        print_gtree($gtree);
    }
    __translate_tree($gtree);
}
########################################################################################
# explore_file & explore_file_line & get_current_line 
#  proc_id : 0110
# argument : none   
#  purpose : process file content before write to target directory   
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited 
#  post    : 
########################################################################################
sub __explore_file(){
    my $line=__get_current_line();
    print "current line is $line\n" if ($debug_mode2);
    __explore_file_line($line);
    $___prev_tl=$line;
    if ($gtree->{current_line} > $gtree->{total_lines}){
        return;
    }else{
        return __explore_file();
    }
}
########################################################################################
# get_current_line 
#  proc_id : 0111
# argument : none   
#  purpose : iterate lines one for each call    
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited 
#  post    : 
########################################################################################
sub __get_current_line(){
    my $idx=$gtree->{current_line};
    my $a=$gtree->{source};
    $gtree->{current_line}=$idx+1;
    return @{$a}[$idx];
}
########################################################################################
# explore_file_line
#  proc_id : 0112
# argument : none   
#  purpose : process file content before write to target directory   
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited 
#  post    : 
########################################################################################
sub __explore_file_line{
    my $tl=$_[0];    
    my $curr_tree=$gtree->{curr_tree};
    
    if (! defined $curr_tree || $curr_tree==$gtree){
        print "gtree->{curr_tree} is root now , gtree->{curr_tree}\n" if ($debug_mode2);
        $curr_tree=$gtree;
    }else{
        print "gtree->{curr_tree} is defined, now is a tree of $gtree->{curr_tree}->{type},\n curr_tree is $gtree->{curr_tree}, parent is $gtree->{curr_tree}->{parent}, gtree is $gtree \n" if ($debug_mode2);
    }
    
    my $nid=$curr_tree->{current_node};

    print "Exploring line $tl\n" if ($debug_mode2);
    if ($curr_tree->{type} eq 'clsdef'){ # classdef lines will be parsed separately when all lines are loaded  
        if ($tl=~/^\s*class\s*}}}\s*$/){
            print "Detected end of class definition.\nStart parsing it and if succeed, will go back to parent node.\n" if ($debug_mode3);
            $curr_tree->{status}='pending-close';
            
            print "Adding reference $curr_tree->{type} of $curr_tree->{var} to cls_defs\n" if $debug_mode;
            $cls_defs->{$curr_tree->{var}}->{r}=$curr_tree; 
            my $old_gtree=$gtree;
            my $olaa=$curr_tree->{raw_lines};
            my $old_subdefs=$sub_defs;
            $cls_defs->{$curr_tree->{var}}->{methods}={};
            $sub_defs=$cls_defs->{$curr_tree->{var}}->{methods};
            __init_gtree($olaa);
            walk_dict($gtree,1,1,"Before process cls_def\n")  if $debug_mode;
            foreach my $tline (@{$olaa}){
                __explore_file_line($tline);
                $___prev_tl=$tline;
            }            
            $curr_tree->{status}='close';
            $cls_defs->{$curr_tree->{var}}->{r}=$gtree; 
            __translate_tree($gtree);
            $gtree->{superclass}=$curr_tree->{superclass};
            $gtree->{type2}='clsdef';
            undef $gtree->{curr_tree};
            walk_dict($cls_defs,1,1,"After process cls_def\n") if $debug_mode;
            $gtree=$old_gtree;
            $sub_defs=$old_subdefs;
            $gtree->{curr_tree}=$curr_tree->{parent};            
            return;
        }
        print "adding plain line into class definition $curr_tree.\n" if ($debug_mode3);
        my $arr=$curr_tree->{raw_lines};
        push(@{$arr},$tl);
        return;       
    }elsif ($curr_tree->{type} eq 'subctrl'){ # sub lines will only be translated each time it is called 
        if ($tl=~/^\s*sub\s*}}}\s*$/){
            print "Detected end of sub definition.\nGo back to parent node.\n" if ($debug_mode4);
            $curr_tree->{status}='close';
            print "Adding reference $curr_tree->{type} of $curr_tree->{var} to sub_defs\n";
            $sub_defs->{$curr_tree->{var}}->{r}=$curr_tree;
            $gtree->{curr_tree}=$curr_tree->{parent};            
            return;
        }
        print "adding plain line into subroutine definition $curr_tree.\n" if ($debug_mode4);
        my $arr=$curr_tree->{raw_lines};
        push(@{$arr},$tl);
        return;       
    }elsif ($tl=~ /{{{\s*foreach(\s+|\Z)/){
        if ($tl=~ /^\s*{{{\s*foreach\s+(\w+)\s+(in)\s+(.+)\Z/){
            print "**** Found foreach structure variable=$1,list=$3\n" if ($debug_mode2);
            $nid++;
            $curr_tree->{nodes}->{$nid}->{t}='f'; # foreach
            my $sub_node={};
            $sub_node->{type}='foreach'; # sub tree
            $sub_node->{current_node}=0;
            $sub_node->{level}=$curr_tree->{level}+1;
            $sub_node->{parent}=$curr_tree;
            $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
            $curr_tree->{current_node}=$nid;
            $sub_node->{list}=$3;
            $sub_node->{var}=$1;
            $sub_node->{status}='open';
            $gtree->{curr_tree}=$sub_node;
            print "continue with sub tree of foreach.\n" if ($debug_mode2);
        }else{
            print "Invalid foreach statement!! Corrent and try again.\n **** $tl";
        }
    }elsif ($tl=~/^\s*foreach\s*}}}\s*\Z/){
        print "**** Found end of foreach structure\n" if ($debug_mode2);
        if (! defined $curr_tree || $curr_tree->{type}!='foreach'){
            die "Error! Found foreach}}}, but it is not in a foreach loop.\n code=$tl\n"; 
        }else{
            ### go back to parent 
            $curr_tree->{status}='close';
            $gtree->{curr_tree}=$curr_tree->{parent};
            print "go back to parent node\n" if ($debug_mode2);
        }
    }elsif ($tl=~ /{{{\s*case(\s+|\Z)/){
        print "**** Found case structure and checking its sub-type\n" if ($debug_mode3);
        if ($tl=~ /^\s*{{{\s*case(\s*)\Z/){ # it's case_condition structure 
            print "**** Found sub-type is case-condition\n" if ($debug_mode3);
            $nid++;
            $curr_tree->{nodes}->{$nid}->{t}='cd'; #   type is case 
            my $sub_node={};
            $sub_node->{type}='ccctrl'; # sub tree is case-switch
            $sub_node->{current_node}=0;
            $sub_node->{level}=$curr_tree->{level}+1;
            $sub_node->{parent}=$curr_tree;
            $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
            $curr_tree->{current_node}=$nid;
            $sub_node->{vartype}='d';
            $sub_node->{status}='open';
            $gtree->{curr_tree}=$sub_node;
            print "continue with sub tree of case-condition.\n" if ($debug_mode2);
        }elsif ($tl=~ /^\s*{{{\s*case\s+(\S+)(.*)\Z/){ # it's possibly a case_switch structure
            $tl=$1.$2; # check content 
            my $tvar;
            my $vtype;
            
            if ($tl=~ /^\s*###\s*(\S+)\s*###\s*\Z/){ # use dynamic stack variable as switch
                print "**** Found sub-type is case-switch, and the switch is dynamic stack variable $1\n" if ($debug_mode3);
                $tvar=$1;
                $vtype='d'; # dynamic;
                $tvar=~s/(^\s+|\s+$)//g;
                $tvar="###$tvar###";
            }elsif ($tl=~ /^(.*){{{(((?!}}}).)*)}}}(.*)\Z/){ # use dynamic function & variable as switch
                print "**** Found sub-type is case-switch, and the switch is dynamic stack variable $1\n" if ($debug_mode3);
                $tvar=$2;
                $vtype='d'; # dynamic;
                $tvar=~s/(^\s+|\s+$)//g;
                $tvar="\{\{\{$tvar\}\}\}";
            }elsif ($tl=~ /^\s*<<<\s*(\S+)\s*>>>\s*\Z/){ # use fixed global variable as switch 
                print "**** Found sub-type is case-switch, and the switch is fixed substitution variable $1\n" if ($debug_mode3);
                $tvar=__fetch_variable($1);
                $tvar=~s/(^\s+|\s+$)//g;
            }else{
                print "**** Error ! case-switch structure can only use <<<substitution variable>>> as switch-variable,\n To use stack variable or other dynamic conditions such as function and expression, you have to use case-condition structure.\n";  
            }
             
            $nid++;
            $curr_tree->{nodes}->{$nid}->{t}='cs'; # caseswitch
            my $sub_node={};
            $sub_node->{type}='csctrl'; # sub tree is case-switch
            $sub_node->{current_node}=0;
            $sub_node->{level}=$curr_tree->{level}+1;
            $sub_node->{parent}=$curr_tree;
            $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
            $curr_tree->{current_node}=$nid;
            $sub_node->{var}=$tvar;
            $sub_node->{vartype}=$vtype;
            $sub_node->{status}='open';
            $gtree->{curr_tree}=$sub_node;
            print "continue with sub tree of case-switch-variable, switch is $tvar.\n" if ($debug_mode2);
        }else{
            print "Invalid foreach statement!! Corrent and try again.\n **** $tl";
        }     
    }elsif ($tl=~ /{{{\s*else\s+then\s*\Z/){
        print "tl is $tl , match anyway.\n" if ($debug_mode3);
        my $ctype=$curr_tree->{type};
        my $vtype=$curr_tree->{vartype};
        print "**** Detected else-branch of case structure\n" if ($debug_mode3);
        if (! defined $curr_tree || ($ctype ne 'csctrl' && $ctype ne 'ccctrl')){
            die "Error! Found {{{else, but it is not in a case structure.\n code=$tl\n"; 
        }elsif ($curr_tree->{status} eq 'close-skip' ) { 
            print "case structure already matched, now it is looking for case}}}\n" if ($debug_mode3);
            $curr_tree->{when_but_skip}=1;
        }else{  
            if ($vtype eq 'd'){
                print ">>>>> adding dynamic else-branch node.\n" if ($debug_mode3 || $debug_mode2);
            }else{
                print ">>>>> condition matches switch, adding branch node.\n" if ($debug_mode3 || $debug_mode2);
            }
            $nid=$curr_tree->{current_node};
            $nid++;
            my $sub_node={};
            $sub_node->{type}='when-branch'; # sub tree
            $sub_node->{stype}='else'; # sub tree
            $sub_node->{current_node}=0;
            $sub_node->{level}=$curr_tree->{level}+1;
            #$sub_node->{parent}=$curr_tree->{parent}; # go to grand-parent as case-when is a 2-layer structure
            $sub_node->{parent}=$curr_tree;
            $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
            $curr_tree->{current_node}=$nid;
            undef $sub_node->{var};
            $sub_node->{status}='open';
            $curr_tree->{status}='in-child';
            print "adding child to $curr_tree->{type} : nid=$nid : status=$curr_tree->{status}, child is $sub_node->{type}\n" if ($debug_mode3);   
            $gtree->{curr_tree}=$sub_node;
        }
    }elsif ($tl=~ /{{{\s*when\s+(.+)\s+then\s*\Z/){
        my $cont=$1;
        $cont=~s/(^\s+|\s+$)//g;
        my $vtype=$curr_tree->{vartype};
        
        print "tl is $tl, cont is $cont, vtype=$vtype\n" if ($debug_mode3);
        my $ctype=$curr_tree->{type};
        
        print "**** Detected when-branch of case structure\n" if ($debug_mode3);
        if (! defined $curr_tree || ($ctype ne 'csctrl' && $ctype ne 'ccctrl')){
            die "Error! Found {{{when, but it is not in a case structure.\n code=$tl\n"; 
        }elsif ($curr_tree->{status} eq 'close-skip' ) { 
            print "case structure already matched, now it is looking for case}}}\n" if ($debug_mode3);
            $curr_tree->{when_but_skip}=1;
        }else{
            print "... ... parse and add child node to $ctype (var=$curr_tree->{var}) \n" if ($debug_mode3);
            
            if ($ctype eq 'csctrl' || $ctype eq 'ccctrl'){
                print "checking $ctype, switch is $curr_tree->{var}, condition is $cont\n" if ($debug_mode3);
                if ($curr_tree->{var} ne $cont && $vtype ne 'd'){ # if dynamic, will collect all branches 
                    $curr_tree->{status}="skip";
                    print ">>>>> condition does not match switch, skipped. $curr_tree->{status} $curr_tree->{type}\n" if ($debug_mode3);
                    return;
                }
                if ($vtype eq 'd'){
                    print ">>>>> adding dynamic branch node.\n" if ($debug_mode3);
                }else{
                    print ">>>>> condition matches switch, adding branch node.\n" if ($debug_mode3);
                }
                $nid=$curr_tree->{current_node};
                $nid++;
                my $sub_node={};
                $sub_node->{type}='when-branch'; # sub tree
                $sub_node->{current_node}=0;
                $sub_node->{cont}=$cont if ($vtype eq 'd');
                $sub_node->{level}=$curr_tree->{level}+1;
                #$sub_node->{parent}=$curr_tree->{parent}; # go to grand-parent as case-when is a 2-layer structure
                $sub_node->{parent}=$curr_tree;
                $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
                $curr_tree->{current_node}=$nid;
                $sub_node->{var}=$curr_tree->{var};
                $sub_node->{status}='open';
                $sub_node->{vartype}=$curr_tree->{vartype};
                $curr_tree->{status}='in-child';
                print "adding child to $curr_tree->{type} : nid=$nid : status=$curr_tree->{status}, child is $sub_node->{type}\n" if ($debug_mode3);   
                $gtree->{curr_tree}=$sub_node;
            }            
        }
    }elsif ($tl=~ /^\s*when\s*}}}\s*\Z/ ){
        print "**** Found end of when structure, $curr_tree->{type} prev_tl=$___prev_tl\n" if ($debug_mode4);
        my $vtype=$curr_tree->{vartype};
        if (! defined $curr_tree || $curr_tree->{type} ne 'when-branch'){
            if ( $curr_tree->{status} eq 'skip' && $curr_tree->{type}=~/csctrl|ccctrl/ ){
                print "End of skipped block, scanning for next branch.\n" if ($debug_mode4);
                $curr_tree->{status}='open';
                return;
            }else{
                print "special place , status=$curr_tree->{status}, type=$curr_tree->{type}\n" if ($debug_mode4);
            }
            if ($curr_tree->{when_but_skip} == 1 ){
                print "current block is being skipping, closed. $tl\n" if ($debug_mode4);
                $curr_tree->{when_but_skip}=0;
            }else{
                die "Error! Found when}}}, but it is not in a when-branch of case structure.\n code=$tl\n";  
            }                
        }else{
            ### go back to parent 
            if ($curr_tree->{type} eq "when-branch"){
                $curr_tree->{status}='close';
                $gtree->{curr_tree}=$curr_tree->{parent};
                print "curr_tree_type=$gtree->{curr_tree}->{type}\n" if ($debug_mode4);
                print "curr_tree_status=$gtree->{curr_tree}->{status}\n" if ($debug_mode4);
                if ($gtree->{curr_tree}->{type}=~ /csctrl|ccctrl/ ){
                    $gtree->{curr_tree}->{status}='close-skip' if ($vtype ne 'd');
                }
                print "curr_tree_type=$gtree->{curr_tree}->{type}\n" if ($debug_mode4);
                print "curr_tree_status=$gtree->{curr_tree}->{status}\n" if ($debug_mode4);
                print "go back to parent node and close\n" if ($debug_mode4);
            }
        }
    }elsif ($tl=~/^\s*case\s*}}}\s*\Z/){
        print "**** Found end of case structure, current type=$curr_tree->{type}, status = $curr_tree->{status} \n" if ($debug_mode2);
        if (defined $curr_tree && $curr_tree->{type} =~ /csctrl|ccctrl/ ){
            if ($curr_tree->{status} =~ /close-skip|open|in-child/ ){
                print ">>> Successful end of case structure. Go back to parent node.\n" if ($debug_mode2);
            }elsif ($curr_tree->{status} eq 'skip'){
                print "**** Error! Found case}}} while when-then statement is not closed. Force close current case structure. line: $tl\n";
            }else{
                print "**** Error! Wrong status of case strucure. Force close current case structure. line: $tl\n";            
            }
            $curr_tree->{status}='close';
            $gtree->{curr_tree}=$curr_tree->{parent};
        }else{
            print "**** Error!! Found invalid case}}}.\n";
            return;
        }
    }elsif ($tl=~ /{{{\s*while\s+/){     
        if ($tl=~ /^\s*{{{\s*while\s+\((.+)\)\Z/){
            print "**** Found while structure condition=$1\n" if ($debug_mode2);
            $nid++;
            $curr_tree->{nodes}->{$nid}->{t}='l'; # while-loop
            my $sub_node={};
            $sub_node->{type}='while'; # sub tree
            $sub_node->{current_node}=0;
            $sub_node->{level}=$curr_tree->{level}+1;
            $sub_node->{parent}=$curr_tree;
            $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
            $curr_tree->{current_node}=$nid;
            $sub_node->{cont}=$1;
            $sub_node->{status}='open';
            $gtree->{curr_tree}=$sub_node;
            print "continue with sub tree of while.\n" if ($debug_mode2);
        }else{
            print "Invalid While statement!! Corrent and try again.\n **** $tl\n correct syntax : \n {{{while (condition)\n ...\n while}}}\n";
        }        
    }elsif ($tl=~/^\s*while\s*}}}\s*\Z/){
        print "**** Found end of while structure\n" if ($debug_mode2);
        if (! defined $curr_tree || $curr_tree->{type}!='while'){
            die "Error! Found while}}}, but it is not in a while loop.\n code=$tl\n"; 
        }else{
            ### go back to parent 
            $curr_tree->{status}='close';
            $gtree->{curr_tree}=$curr_tree->{parent};
            print "go back to parent node\n" if ($debug_mode2);
        }
    }elsif ($tl=~/{{{\s*sub\s+(\w+)\((.*)\)\s*$/){
        my $subname=$1;
        my $arglist=$2;

        print "**** Found subroutine definition $subname, start parsing...\n" if ($debug_mode);
            
        $arglist=~s/^\s+|\s+$//g;
        my @arg_arr=split(/,/,$arglist);
        my $arg;
        
        for my $ai (1..$#arg_arr){
            $arg=$arg_arr[$ai-1];
            $arg=~s/^\s+|\s+$//g;
            if ($arg=~/\W+/){
                print "**** Error ! Invalid argument , stop parsing subroutine $subname\n";
                return; 
            }
            $arg_arr[$ai-1]=$arg;
        }
        
        print "arglist is @arg_arr\n" if ($debug_mode3);
        
        $nid++;
        $curr_tree->{nodes}->{$nid}->{t}='subdef'; # caseswitch
        my $sub_node={};
        $sub_node->{type}='subctrl'; # sub tree is case-switch
        $sub_node->{var}=$subname;
        $sub_node->{current_node}=0;
        $sub_node->{level}=$curr_tree->{level}+1;
        $sub_node->{parent}=$curr_tree;
        $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
        $curr_tree->{current_node}=$nid;
        $sub_node->{arglist}=\@arg_arr;
        my @arr=();
        $sub_node->{raw_lines}=\@arr;
        $sub_node->{status}='open';
        $gtree->{curr_tree}=$sub_node;
        print "continue with subroutine definition : $subname.\n" if ($debug_mode2);
    }elsif ($tl=~/{{{\s*class\s+(\w+)\s*(.*)\s*$/){
        my $classname=$1;
        my $arglist=$2;
        my $superclass=undef;

        print "**** Found class definition $classname, start parsing...\n" if ($debug_mode);
        $arglist=~s/^\s+|\s+$//g;
        
        if ($arglist=~/\s*\:\s*(\w+)\s*$/){
            $superclass=$1;
        }
        $nid++;
        $curr_tree->{nodes}->{$nid}->{t}='classdef'; # class definition
        my $sub_node={};
        $sub_node->{type}='clsdef'; # sub tree is case-switch
        $sub_node->{var}=$classname;
        $sub_node->{current_node}=0;
        $sub_node->{level}=$curr_tree->{level}+1;
        $sub_node->{parent}=$curr_tree;
        $curr_tree->{nodes}->{$nid}->{r}=$sub_node;
        $curr_tree->{current_node}=$nid;
        $sub_node->{superclass}=$superclass;
        my @arr=();
        $sub_node->{raw_lines}=\@arr;
        $sub_node->{status}='open';
        $gtree->{curr_tree}=$sub_node;
        print "continue with class definition : $classname.\n" if ($debug_mode2);
    }else{
        my $mtype=$curr_tree->{type};
        
        print "plain line is being analyzed type=$mtype, status=$curr_tree->{status}\n" if ($debug_mode3);
        
        if ($mtype =~ /csctrl|ccctrl/){
            if ($curr_tree->{status} eq 'skip'){
                print "skipping unmatched block line : $tl\n" if ($debug_mode3);
            }elsif ($curr_tree->{status} eq 'close-skip'){
                print "case result is already matched, skipping the rest.\n" if ($debug_mode3);
            }else{
                print "**** Error : Invalid Line, 'when-then' statement is missing : $tl\n";
            }
            return;
        }
              
        $nid++;
        print "plain line, adding to node $nid\n" if ($debug_mode2);
        $curr_tree->{nodes}->{$nid}->{t}='p'; # type=plain text
        $curr_tree->{nodes}->{$nid}->{s}=$tl; # source
        $curr_tree->{current_node}=$nid;
    }
}
########################################################################################
# translate_tree 
#  proc_id : 0120
# argument : none   
#  purpose : process file content before write to target directory   
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited 
#  post    : 
########################################################################################
sub __translate_tree{
    my $ct=$_[0];
    my $fl;
    print "Translating tree $ct...\n" if ($debug_mode2);
    if (defined $ct){
        my $nodes=$ct->{nodes};
        if (defined $nodes){
            my $level=$ct->{level};
            my $pstr=pad_t($level+2,'-');
            my $skipped=0;
            foreach my $k ( sort { $a <=> $b } keys %{$nodes}){
                if ($nodes->{$k}->{t} eq 'p'){
                    $fl=$nodes->{$k}->{s};
                    print "old line is $fl\n" if ($debug_mode2);
                    $skipped=is_skipped($fl);
                    print "translating stacked variables....\n" if ($debug_mode2);
                    $fl=__translate_stacked_vars($fl,$ct);
                    print "translated line is $fl \n" if ($debug_mode2);
                    $fl=__substitute_string($fl);
                    print "new line is $fl\n"  if ($debug_mode2);
                    $nodes->{$k}->{n}=$fl;
                    print "nlines is $gtree->{nlines}, fl is $fl\n" if ($debug_mode2);
                    my @nlines=@{$gtree->{nlines}};
                    print "before push $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
                    push(@{$gtree->{nlines}},$fl) if (!$skipped);
                    print "after push $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
                }else{
                    my $ptr=$nodes->{$k};
                    my $sub=$ptr->{r};
                    if (defined $sub){
                        ## dig into sub nodes     
                        print "Drill into sub nodes $sub...\n" if ($debug_mode2);
                        print " type is $sub->{type}, var is $sub->{var}, list is $sub->{list}\n" if ($debug_mode);
                        if ($sub->{type} eq 'foreach'){
                            print "Fetching variable $sub->{var} from $sub->{list}\n" if ($debug_mode2);
                            my $va=$sub->{list};
                            my $vb;
                            my $vc;
                            if ($va=~/{{{get_hash_value\s+(\w+)\s+(.+)}}}/){ # function call get_hash_value 
                                my $vb=$1;
                                my $vc=$2;
                                print "get_hash_value: hashname is $vb, key is $vc\n" if ($debug_mode2);
                                $vb=__get_variable_in_scope($vb,$sub);
                                
                                if (defined $vb && ref $vb){
                                    print "final hash obj is located : $vb\n" if ($debug_mode2);
                                    $vc=__get_variable_in_scope($vc,$sub);
                                    print "final key value is $vc\n" if ($debug_mode2);
                                    $vc=$vb->{$vc};
                                    print "final data is $vc\n" if ($debug_mode2);
                                    
                                    if (ref $vc){
                                        print "     got reference\n" if ($debug_mode2);
                                        my @arr=@{$vc};
                                        my $oldv=$sub->{stack}->{$sub->{var}};
                                        foreach my $v (@arr){
                                            print " Assign $v to $sub->{var} ... \n" if ($debug_mode2);
                                            $sub->{stack}->{$sub->{var}}=$v;
                                            __translate_tree($sub);
                                        }
                                        if (defined $oldv){
                                            $sub->{stack}->{$sub->{var}}=$oldv;
                                        }else{
                                            undef $sub->{stack}->{$sub->{var}};
                                        }
                                    }else{
                                        print "****** Error ! Cannot find hash object $vb  ****** \n";
                                    }
                                    
                                }else{
                                    print "****** Error ! Cannot find hash object $vb  ****** \n";                                
                                }
                            }elsif ($va=~/{{{hash_keys\s+(\S+)\s*}}}/ 
                                 || $va=~/{{{hash_keys\s+(\S+)\s+(\S+)\s*}}}/ 
                                 || $va=~/{{{hash_keys\s+(\S+)\s+(\S+)\s+(\S+)\s*}}}/){ 
                                 # function call hash_keys, need to change to call a function named hash_keys 
                                $vb=$1;
                                my $sk2=$2;
                                my $sk3=$3;
                                # before parsing, do final substitution   
                                $vb=__substitute_string($vb);
                                $vc=__fetch_stacked_vars($vb,$sub);
                                if (! ref $vc ){ # convert it to ref 
                                    $vc=__fetch_stacked_vars($vc);
                                }
                                if (!ref $vc){
                                    print "Invalid list $vc in foreach statement\n";
                                }
                                print "fetching local stacked variable from $vc by key $sk2 and its child $sk3\n" if ($debug_mode);
                                print "--> $vc\n" if ($debug_mode);
                                
                                if (defined $sk2){
                                    $sk2=__get_variable_in_scope($sk2);
                                    $sk3=__get_variable_in_scope($sk3);
                                }
                                print "sk2=$sk2, sk3=$sk3 \n" if ($debug_mode && $verbose_mode);
                                
                                if (ref $vc){
                                    if (defined $sk3){
                                        $vc=$vc->{$sk2}->{$sk3};
                                    }elsif (defined $sk2){
                                        $vc=$vc->{$sk2};
                                    }                               
                                }
                                
                                if (defined $vc && ref $vc){
                                    my @arr;
                                    if (ref $vc eq 'HASH'){
                                        @arr= keys %$vc;
                                    }else{
                                        @arr=@$vc;
                                    }
                                    print "     got reference\n" if ($debug_mode2);
                                    print "Enter loop \n" if ($debug_mode2);

                                    my $oldv=__get_value_in_stack($sub->{var},$gtree->{curr_tree});
                                    foreach my $v (@arr){
                                        print " Assign $v to $sub->{var} ... \n" if ($debug_mode2);
                                        __push_stack_vars($sub->{var},$v,$gtree->{curr_tree});
                                        __translate_tree($sub);
                                    }
                                    __restore_value_in_stack($sub->{var},$oldv,$gtree->{curr_tree});
                                }else{
                                    print "****** Error ! could not found array for $vb ****** \n";
                                }
                            }elsif ($va=~/{{{\s*range(.+)}}}/){# range function 
                                print("range function is called $va\n") if $debug_mode;
                                $va=__run_func('range',$1);
                                print("range function result after called @{$va}\n") if $debug_mode;
                                my $oldv=__get_value_in_stack($sub->{var},$gtree->{curr_tree});
                                foreach my $v (@$va){
                                    print " Assign $v to $sub->{var} ... \n" if ($debug_mode2);
                                    __push_stack_vars($sub->{var},$v,$gtree->{curr_tree});
                                    __translate_tree($sub);
                                }
                                __restore_value_in_stack($sub->{var},$oldv,$gtree->{curr_tree});
                            }elsif ($va=~/\<\<\<\s*(\w+)\s*\>\>\>/){# if it is key name
                                $vb=$1;
                                $vc=__fetch_variable($vb);
                                print "--> $vc\n" if ($debug_mode2);
                                if (ref $vc){
                                    print "     got reference\n" if ($debug_mode2);
                                    my @arr;
                                    if (ref $vc eq 'HASH'){
                                        @arr= keys %$vc;
                                    }else{
                                        @arr=@{$vc};
                                    }
                                    my $oldv=__get_value_in_stack($sub->{var},$gtree->{curr_tree});
                                    foreach my $v (@arr){
                                        print " Assign $v to $sub->{var} ... \n" if ($debug_mode2);
                                        __push_stack_vars($sub->{var},$v,$gtree->{curr_tree});
                                        __translate_tree($sub);
                                    }
                                    __restore_value_in_stack($sub->{var},$oldv,$gtree->{curr_tree});
                                }else{
                                    print "****** Error ! could not found array for $vb ****** \n";
                                }
                            }elsif ($va=~/###\s*(\w+)\s*###/){#if it is defined tree stack variable 
                                $vb=$1;
                                $vc=__fetch_stacked_vars($vb,$sub);
                                print "fetching local stacked variable $vc\n" if ($debug_mode2);
                                print "--> $vc\n" if ($debug_mode2);
                                
                                my $typ=ref $vc;
                                if ($typ){
                                    print "     got reference\n" if ($debug_mode2);
                                    my @arr;
                                    if ($typ eq 'HASH') {
                                        @arr=values %$vc
                                    }elsif ($typ eq 'ARRAY') {
                                        @arr=@{$typ}
                                    }
                                    
                                    my $oldv=__get_value_in_stack($sub->{var},$gtree->{curr_tree});
                                    foreach my $v (@arr){
                                        print " Assign $v to $sub->{var} ... \n" if ($debug_mode2);
                                        __push_stack_vars($sub->{var},$v,$gtree->{curr_tree});
                                        __translate_tree($sub);
                                    }
                                    __restore_value_in_stack($sub->{var},$oldv,$gtree->{curr_tree});
                                }else{
                                    print "****** Error ! could not found array for $vb ****** \n";
                                }
                            }
                        }elsif ($sub->{type}=~/csctrl|ccctrl/){
                            print "Exploring case structure sub=$sub, t=$sub->{t}, type=$sub->{type}, status=$sub->{status}, r=$sub->{nodes}->{0}->{r}, nodes=$sub->{nodes} \n" if ($debug_mode3);
                            my $tj=$sub->{nodes}->{0}->{r}; # workaround for perl issue, otherwise, below statement won't get accurate number 
                            #print "$sub->{nodes}\n";
                            my @nodes=keys %{$sub->{nodes}};
                            print "@nodes\n" if ($debug_mode3);
                            for my $ik (1..$#nodes){
                                my $snh=$sub->{nodes}->{$ik}->{r}; # there should be only one child 
                                my $vtype=$snh->{vartype};
                                print "!!!!!!!!!!!!!!!!!!!!!!!!!!! snh.type=$snh->{type},snh.vtype=$snh->{vartype}, snh.cont=$snh->{cont}\n" if ($debug_mode3); 
                                if ($vtype eq 'd'){
                                    # checking conditon 
                                    my $cont=$snh->{cont};
                                    my $var=$snh->{var};
                                    if (defined $var){
                                        my $oldcr=$gtree->{curr_tree};
                                        $gtree->{curr_tree}=$snh;
                                        $var=__translate_stacked_vars($var,$sub);
                                        $var=__substitute_string($var);
                                        print "convert var to $var\n" if ($debug_mode3);
                                        $cont=__substitute_string($cont);
                                        print "substituted cont is $cont\n" if ($debug_mode3);
                                        $gtree->{curr_tree}=$oldcr;
                                    }
                                    if ($sub->{type} eq 'csctrl'){
                                        if ($var eq $cont){
                                            __translate_tree($snh);
                                            last;
                                        }
                                    }elsif ($sub->{type} eq 'ccctrl'){
                                        $cont=__translate_stacked_vars($cont,$sub);
                                        $cont=__substitute_string($cont);
                                        print "evaluate condition $cont\n";
                                        $cont=reval_expr($cont);
                                        print "result is $cont\n";
                                        if ($cont){
                                            __translate_tree($snh);
                                            last;
                                        }
                                    }
                                }else{
                                    __translate_tree($snh);
                                }
                            }
                        }elsif ($sub->{type} eq 'while'){
                            print "Exploring while structure sub=$sub, t=$sub->{t}, type=$sub->{type}, status=$sub->{status}, r=$sub->{nodes}->{0}->{r}, nodes=$sub->{nodes} \n" if ($debug_mode3);
                            my $tj=$sub->{nodes}->{0}->{r}; # workaround for perl issue, otherwise, below statement won't get accurate number 
                            #print "$sub->{nodes}\n";
                            my @nodes=keys %{$sub->{nodes}};
                            print "@nodes\n" if ($debug_mode3);                            
                            my $cont=$sub->{cont};
                            print "cont is $cont\n" if $debug_mode3;
                            my $cont2=__substitute_string($cont);
                            my $j=0;
                            while (reval_expr($cont2) && $j<$__loop_lmt){
                                print "cont state is ". reval_expr($cont2) ."\n" if $debug_mode3;
                                __translate_tree($sub);
                                $cont2=__substitute_string($cont);
                                $j++;
                            }
                        }                        
                    }else{
                        print "Something is wrong, r is defined in $sub->{r}\n" if ($debug_mode2);
                    }
                }
            }
        }
    }    
}
########################################################################################
# is_skipped 
#  proc_id : 0130
# argument : none   
#  purpose : mark the lines that do not need to appear in the final file    
#  pre     : none 
#  post    : return 1 for those lines that only take some actions and do not produce lines 
########################################################################################
sub is_skipped{
    my $p=$_[0];
    if ($p=~/^\s*\{\{\{(\S+)\s*/){$p=$1;
    return 1 if ($p eq 'define' || $p eq 'push_hash' || $p eq 'mute' || $p eq 'skip' || $p eq 'ref' || $p eq 'set' || $p eq 'sub' || $p eq 'get_args' || $p eq 'fi_gen2' || $p eq 'fo_chmod' || $p =~ /^\s*\#/);
    }
    return 0;
}
########################################################################################
# translate_stacked_vars 
#  proc_id : 0140
# argument : 1. origin line  2.current tree node   
#  purpose : translate the string which has stack variable value (not the global substitution variable)    
#  pre     :  
#  post    : return 1 for those lines that only take some actions and do not produce lines 
########################################################################################
sub __translate_stacked_vars{
    my $fl=$_[0];
    my $sub=$_[1];
    my $result=$fl;
   #   stopped here at 1/19/2021 
    if (!defined $sub){
        $sub=$gtree->{curr_tree};
        if (!defined $sub){
            $sub=$gtree;
        }
    }
    print "sub:translate_stacked_vars:fl=$fl,sub=$sub\n" if ($debug_mode2 || ($debug_mode && $verbose_mode) );
    
    if ($fl=~/^(((?!###).)*)\#\#\#(\w+)\#\#\#(.*)$/){
        print "variable caught\n" if ($debug_mode2);
        print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6 translated_stacked_vars\n" if ($debug_mode) ;
        my $h=$1;
        my $c=$3;
        my $t=$4;
        #$h=translate_stacked_vars($h,$sub);
        #$c=sweep_stack($c,$sub);
        $c=__fetch_stacked_vars($c,$sub);
        my $typ=ref $c;
        if ($typ=~/(ARRAY|HASH)/){
            print "It is array/hash ref, saving to stack_func_refs\n" if ($debug_mode);
            $c=__stack_func_ref($c);
            $c=" ###$c### ";
        }
        $t=__translate_stacked_vars($t,$sub);
        $fl=$h.$c.$t;
        return __translate_stacked_vars($fl); # translate again, in case it has formed new variables dynamically.
    }
    return $fl; # give up 
}
########################################################################################
# fetch_stacked_vars 
#  proc_id : 0141
# argument : 1. variable name  2.current tree node   
#  purpose : get value of provided stack variable name     
#  pre     : variable is stacked in the tree node or its ancesters 
#  post    :  
########################################################################################
sub __fetch_stacked_vars{
    my $fl=$_[0];
    my $sub=$_[1];    
    my $final=0;
    if ($fl=~/^\s*\###(((?!###).)+)###\s*$/){
        $fl=$1;
    }
    print "fetching fl=$fl, sub=$sub\n" if ($debug_mode || $debug_mode2);
    
    if (!defined $sub){
        $sub=$gtree->{curr_tree};
    }
    
    if ($sub==$gtree || !defined $sub){
        $sub=$gtree;
        $final=1;
    }

    
    my $var=$sub->{stack}->{$fl};
    
    print "var is $var\n" if ($debug_mode || $debug_mode2);
    
    #walk_dict($sub,1,1,'sub in fetch_stacked_vars');
    print("fetching $fl with $sub , $sub->{super}\n") if $debug_mode;
    
    if (defined $var){
        return $var;
    }elsif (defined $sub->{super} ){# && $sub->{r}->{type2} eq 'clsdef'){
        walk_dict($sub,1,1,'sub in fetch_stacked_vars');
        $var=__fetch_stacked_vars($fl,$sub->{super}->{r});
        return $var if (defined $var);
    }
    
    if ($sub == $gtree){    
        #checking mapping as last resort 
        my $mapped=$ref_params->{$fl};
        
        print "mapped=$mapped, $mapped->{name}\n" if ($debug_mode);
 
        if (!defined $mapped || ! defined $mapped->{name}){
            return $fl;
        }else{
            return $app_params->{$mapped->{name}};
        }
    }else{
        return __fetch_stacked_vars($fl,$sub->{parent}) if (!$final);
    }
    return $fl;
}
########################################################################################
# stack_func_ref 
#  proc_id : 0150
# argument : array ref or hash ref     
#  purpose : stack array ref or hash ref into subroutine's stack  
#  pre     :   
#  post    : when extract from stack, use special format for variable name --> ????variable-name????  
########################################################################################
sub __stack_func_ref{
    my $fl=$_[0];
    my $sub=$_[1];

    if (!defined $sub){
        $sub=$gtree->{curr_tree};
        $sub=$gtree if (!defined $sub);
    }
    print "stacking $fl to $sub\n" if ($debug_mode && $verbose_mode);
    $sub->{stack}->{"????$fl????"}=$fl;
    return "????$fl????";
}
########################################################################################
# get_variable_in_scope 
#  proc_id : 0160
# argument : a global substitution variable name or a stacked variable name   
#  purpose : find value of a global substitution name or a stacked variable name 
#            convinient way to get check both in one routine   
#  pre     : $gtree is properly inited, $gtree->{curr_tree} is set to the node currently being processed   
#  post    : return the value of variable if found otherwise return null 
########################################################################################
sub __get_variable_in_scope{
    my $va=$_[0];
    my $sub=$_[1];
    my $vb;
    my $vc;
    
    return if (! defined $va);
    $sub=$gtree if (! defined $sub);
    
    print "$va is passed in get_variable_in_scope\n" if ($debug_mode);
    
    if ($va=~/\<\<\<\s*(\w+)\s*\>\>\>/){# if it is key name
        return $app_params->{$1};
    }elsif ($va=~/\#\#\#\s*(\w+)\s*\#\#\#/){#if it is defined tree stack variable
        $vb=$1;
        print "going to pass $vb into fetch_stacked_vars\n" if ($debug_mode2);
        return __fetch_stacked_vars($vb,$sub);
    }elsif ($va=~/^\s*(\w+)\s*$/){
       $vb=$1;
        print "bare word $va is passed into get_variable_in_scope\n" if ($debug_mode2);
        return __fetch_stacked_vars($vb,$sub);
    }elsif ($va=~/\#\#\#(\?\?\?\?(HASH|ARRAY)\(0x[A-Fa-f0-9]+\)\?\?\?\?)\#\#\#/){
       $vb=$1;
       print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5 \nobject ref is detected, will trying get_func_ref\n" if ($debug_mode2);
       return __fetch_stacked_vars($vb,$sub);
    }
}
########################################################################################
# get_value_in_stack 
#  proc_id : 0170
# argument : variable name & current gtree node    
#  purpose : get variable from the gtree node only. Not from its ancesters or decendants
#            this is different from fetch_stacked_vars, the latter traverses all ancesters (still not for decendants)   
#  pre     : $gtree is properly inited, $sub is the node to be accessed    
#  post    : return null if the variable not in current node's stack  
########################################################################################
sub __get_value_in_stack{
    my $fl=$_[0];
    my $sub=$_[2];
    return if (!defined $sub || !defined $fl || ! defined $sub->{stack});    
    return $sub->{stack}->{$fl};
}
########################################################################################
# push_stack_vars 
#  proc_id : 0180
# argument : variable name & value & current gtree node    
#  purpose : push variable to the stack of gtree node. 
#  pre     : $gtree is properly inited, $sub is the node to be accessed    
#  post    : the value in stack can be accessed   
########################################################################################
sub __push_stack_vars{
    my $fl=$_[0];
    my $vl=$_[1];
    my $sub=$_[2];
    if (!defined $sub){
        $sub=$gtree->{curr_tree};
        if (!defined $sub){
            $sub=$gtree;
        }
    }
    $sub->{stack}->{$fl}=$vl;
    print "pushed value of $fl with $vl to $sub, $gtree->{curr_tree}, sub.parent $sub->{parent}\n" if ($debug_mode);
}
########################################################################################
# restore_value_in_stack 
#  proc_id : 0190
# argument : variable name & value & current gtree node    
#  purpose : restore the origin state of stack of the gtree node (undef it if neccessary) 
#  pre     : $gtree is properly inited, $sub is the node to be accessed    
#  post    : the old state of stack variable is restored
#  note    : at the moment, it is not saving/restoring the whole stack in one-call   
########################################################################################
sub __restore_value_in_stack{
    my $fl=$_[0];
    my $vl=$_[1];
    my $sub=$_[2];
    
    return if (!defined $sub);
    
    if (!defined $vl){
        undef $sub->{stack}->{$fl};
    }else{
        $sub->{stack}->{$fl}=$vl;
    }
}
########################################################################################
# fetch_variable  
#  proc_id : 0200
# argument : global substitution variable name     
#  purpose : get value of global substitution variable name
#  pre     : parse_template is called, get_variable_values is called     
#  post    : return value found 
#  note    : the name of this subroutine does not have "stacked"   
########################################################################################
sub __fetch_variable{
    my $key=$_[0];
    my $value=$app_params->{$key};
    print "substitute key : $key --> value:$value\n" if ($debug_mode);
    print "!!!!!! Couldn't find value for $key !!!!!\n" if ($value =~ /^\s*$/ && $debug_mode);
    return $value;
}
########################################################################################
# __run_func
#  proc_id : 0210
# argument : function name and arguments
#  purpose : to process tssml function
#  pre     : $gtree is properly inited
#  post    : process or call other utility subroutine accordingly
#  note    :
########################################################################################
sub __run_func{
    my $f=$_[0];
    my $p=$_[1];
    my $orig=$_[2];
    print "__run_func is called f=$f,p=$p,orig=$orig\n" if ($debug_mode3);

    if ($f !~ /\S+/){
        print "no function name is passed, return\n" if ($debug_mode3);
        return;
    }elsif ($f eq 'define'){ #{{{define}}}
        print "Defining local variables $p\n" if ($debug_mode);
        __parse_local_def($p);
        return ''; # define will hide the line from output
    }elsif ($f eq 'skip'){ # do not process the line #{{{skip}}} 
        return;
    }elsif ($f eq 'thru'){ # do nothing and return original #{{{thru}}}
        return $p;
    }elsif ($f eq 'mute'){#{{{mute}}}
        return;
    }elsif ($f eq 'ref'){ # references stacked variable to global variable#{{{ref}}}
        $ref_params={} if (!defined $ref_params);
        if ($p=~ /^\s*(\w+)\s+(\w+)\s*$/){
            $ref_params->{$1}->{name}=$2; # name = text, ref = object ref
        }
        return; # hide line from output
    }elsif ($f=~/set/){ # variable assignment #{{{set}}}
        __parse_var_assignment($p);
        return;
    }elsif ($f eq 'get'){#{{{get}}}
        return __parse_var_retrieval($p);
    }elsif ($f=~/push_hash/){#{{{push_hash}}}
        __push_local_hash_def($p);
        return; # push hash will hide the line from output
    }elsif ($f eq 'iif'){ #{{{iif}}} # if inline
        print "p=$p in iff function\n" if ($debug_mode3);
        $p=~s/^\s+|\s+$//g;
        my @tparr=split(/\s+/,$p);
        my $tpvar=$tparr[0];
        my $tplen=$#tparr;
        my $tpl="value=$tpvar";
        my $m=0;
        my $ret='';
        for my $j (1..$tplen){
            if ($j % 2 == 1){
                if ($j!=$tplen){
                    $tpl.=",ifmatch=$tparr[$j]";
                    if ($tpvar eq $tparr[$j] || $tpvar == $tparr[$j] ){
                        $m=1;
                    }
                }else{
                    $tpl.=",else=$tparr[$j]";
                    $ret= $tparr[$j];
                }
            }else{
                $tpl.=",return=$tparr[$j];";
                if ($m){
                    $ret=$tparr[$j];
                    last;
                }
            }
        }
        print "$tpl, ret=$ret\n" if ($debug_mode3);
        return $ret;
    }elsif ($f eq 'expr'){#{{{expr}}}
        print ">>Calling expr >>>>before reval , before translate expr is $p\n" if ($debug_mode3);
        $p=__translate_stacked_vars($p);
        $p=__substitute_string($p);
        print ">>Calling expr >>>>before reval , after last translate expr is $p\n" if ($debug_mode3);
        return reval_expr($p);
    }elsif ($f eq 'hash_keys'){#{{{hash_keys}}}
        print "Calling hash_keys function p=$p\n" if ($debug_mode);
        $p =~ s/^\s+|\s+$//g;
        my @pars=split(/\s+/,$p);
        my $hash=$pars[0];
        my $key1=$pars[1];
        my $key2=$pars[2];
        my $key3=$pars[3];
        my $key4=$pars[4];
        print "1st: hash=$hash key1=$key1 key2=$key2 key3=$key3 key4=$key4 \n" if ($debug_mode);
        $hash=__get_variable_in_scope($hash);
        $key1=__get_variable_in_scope($key1);
        $key2=__get_variable_in_scope($key2);
        print "2nd: hash=$hash key1=$key1 key2=$key2 key3=$key3 key4=$key4 \n" if ($debug_mode);

        print "hash is $hash\n" if ($debug_mode);

        my $ret;
        if (defined $key4){
            $ret= $hash->{$key1}->{$key2}->{$key3}->{$key4};
        }elsif (defined $key3){
            $ret= $hash->{$key1}->{$key2}->{$key3};
        }elsif (defined $key2){
            $ret= $hash->{$key1}->{$key2};
        }elsif (defined $key1){
            $ret= $hash->{$key1};
        }

        print "returning $ret\n" if ($debug_mode);

        return $ret;
    }elsif ($f eq 'contains'){
        print "Calling in_list function p=$p\n" if ($debug_mode);
        $p =~ s/^\s+|\s+$//g;
        my @pars=split(/\s+/,$p);     
        my $checker=$pars[0];
        my $pouch=$pars[1];
        print "1st: checker=$checker pouch=$pouch \n" if ($debug_mode);
        $checker=__get_variable_in_scope($checker);
        $pouch=__get_variable_in_scope($pouch);
        print "2nd: checker=$checker pouch=$pouch \n" if ($debug_mode);
        
        print "checker is $checker\n" if ($debug_mode);

        if (ref $pouch eq 'ARRAY'){
            if ( grep { $_ eq $checker } @$pouch){
                return 1;
            }
        }elsif (ref $pouch eq 'HASH'){
            return 1 if defined $pouch->{$checker};
        }
        return 0;        
    }elsif ($f eq 'fields'){
            my @pars=split(/\s+/,$p);
            my $fdef=$pars[0];
            my $dlm=$pars[1];
            my $dlm2=$pars[2];
            my $dat=join " ", @pars[3 .. $#pars];
            
            my @arr=();
            my @farr=split(',',$fdef);
            if ($dlm eq '[space]'){
                @arr=split(/\s+/,$dat);
            }else{
                @arr=split($dlm,$dat);
            }
            my $str='';
            foreach my $i (@farr){
                $str.=$arr[$i];
                if ($dlm2 eq '[space]'){
                    $str.=' ';
                }else{
                    $str.=$dlm2;
                }
            }
            chop($str);
            return $str;
    }elsif ($f=~/flat_list(_f|\s*)/){#{{{flat_list}}}
        my $typ=$1;
        if ($typ eq '_f'){
            my @pars=split(/\s+/,$p);
            my $str=$pars[0];
            my $dlm=$pars[1];
            my $fuc=$pars[2];
            print "list is $str, delimiter is $dlm, function is $fuc\n" if ($debug_mode && $verbose_mode);
            if ($str=~/\#\#\#(\S+)\#\#\#/){
                $str=$1;
                my $list=__fetch_stacked_vars($str);
                #print "list is $list\n";
                $str=ref $list;
                if ($str=~/HASH/){
                    my @tar=keys %{$list};
                    for my $idx (0..$#tar){
                        $str=$tar[$idx];
                        $tar[$idx]=__run_func($fuc,$str);
                    }
                    $str=join(",",@tar);
                }elsif ($str=~/ARRAY/){
                    print "it is array\n" if ($debug_mode && $verbose_mode);
                }else{
                    print "it is not ref\n" if ($debug_mode && $verbose_mode);
                }
                return $str;
            }elsif($str=~/<<<(\S+)>>>/){
                my $list=__substitute_string($str);
                $list=__fetch_stacked_vars($str);
                print("list=$list\n");
                $str=ref $list;
                if ($str=~/HASH/){
                    my @tar=keys %{$list};
                    for my $idx (0..$#tar){
                        $str=$tar[$idx];
                        $tar[$idx]=__run_func($fuc,$str);
                    }
                    $str=join(",",@tar);
                }elsif ($str=~/ARRAY/){
                    print "it is array\n" if ($debug_mode && $verbose_mode);
                }else{
                    print "it is not ref\n" if ($debug_mode && $verbose_mode);
                }
                return $str;            
            }
        }
    }elsif ($f=~/sub_(l|r)(\d+)/){#{{{sub_l or sub_r}}}
        my $pos=$1;
        my $len=$2;
        if ($pos eq 'r'){
            my $len2=(0-$len);
            return substr($p,$len2);
        }else{
            return substr($p,0,$len);
        }
    }elsif ($f=~/sub_m_(\d+)_(\d+)/){#{{{sub_m}}}
        my $p1=$1;
        my $p2=$2;
        return substr($p,$p1-1,$p2-$p1+1);
    }elsif ($f=~/pad_(t|s)(\d+)/){#{{{pad_t or pad_s}}}
        my $pos=$1;
        my $len=$2;
        my @pp=();
        if ($pos eq 't'){
            push(@pp,$len);
            push(@pp,split(/\s+/,$p));
            return pad_t(@pp);
        }elsif ($pos eq 's'){
            push(@pp,$len);
            push(@pp,split(/\s+/,$p));
            return pad_s(@pp);
        }else{
            push(@pp,$len);
            push(@pp,split(/\s+/,$p));
            return pad_s(@pp);
        }
    }elsif  ($f eq 'lc'){#{{{lc}}}
        return lc $p;
    }elsif ($f eq 'uc'){#{{{uc}}}
        return uc $p;
    }elsif ($f=~/wrap_lst_(ht|st)(\d+)\Z/){#{{{wrap_lst}}}
        my $opt=$1;
        my $len2=$2;
        print "$f: parameter passed in :  $p opt=$opt,len=$len2\n" if ($debug_mode);
        if ($opt eq 'ht'){
            if ($p =~ /(.*)(ARRAY\(0x\w+\))(.*)/){
                my $astr=$2;
                my $aref=$arr_refs->{$astr};
                my $result;
                my $ttp;
                print "Detect array ref $aref\n" if (ref $aref eq 'ARRAY' && $debug_mode);
                foreach my $al (@{$aref}){
                    $ttp=$p;
                    print "al=$al,p=$p,astr=$astr\n" if ($debug_mode);
                    $al=pad_s($len2,$al);
                    $ttp =~ s/\Q$astr/$al/;
                    $result.="$ttp\n";
                }
                chomp($result);
                return $result;
            }
        }else{
            print "**** Error ! Unknown function name $f !!!!!\n";
        }
    }elsif ($f=~/^\#/){
        return; # this is comment, skip
    }elsif ($f=~/diff_update/){#{{{diff_update}}}
        print "to diff_update a file $p, orig=$orig, sub_depth=$sub_depth\n" if ($debug_mode);
        my @nlines;
        my @olines;
        my @ulines;
        my $template=$gsets->{template_selected};
        my $cwd=$gsets->{cwd};
        my $target=$gsets->{target};
        my $dirname=$gsets->{template_dir};

       if ($sub_depth!=0){
            print "!!!Error!!!, diff_update can only be used for file name substitution not file content.\n";
            exit 0;
       }

        print "source file is $dirname/$template/\{\{\{$orig\}\}\}\n" if ($debug_mode);

        my $ret=exit_when_not_found("$target/$p",1);

        if ($ret){
            print "Skip.\n";
            $sub_depth=-2;
            return;
        }

        $ret=catfile($dirname,$template);
        $ret=catfile($ret,"\{\{\{$orig\}\}\}");
        open(FS, '<', $ret) or die $!;
        chomp(my @nlines = <FS>);
        close FS;

        open(FT, '<', catfile($target,$p)) or die $!;
        chomp(my @olines = <FT>);
        close FT;

        print "Comparing files and update if required...\n";

        foreach my $tl1 (@nlines){
            my $tl=__substitute_string($tl1);
            if ($debug_mode){
                print ">>> comparing $tl\n";
            }
            my $m=0;
            foreach my $tl2(@olines){
                if ($tl eq $tl2){
                    $m=1;
                    print "line exists, skip\n" if ($debug_mode);
                }
            }
            print "found new line $tl\n" if ($debug_mode && !$m);
            push(@ulines,$tl) if (!$m);
        }

        open(FU, '>>', catfile($target,$p)) or die $!;
        if ((scalar @ulines)>0){

            print FU "##################################################\n";
            print FU "##### Below lines are added by menusetup.pl ######\n";
            print FU "##################################################\n";

            foreach my $ul (@ulines){
                print "writing $ul \n" if ($debug_mode);
                print FU "$ul\n";
            }
            print "write ".(scalar @ulines)." lines into $target/$p\n\n";
        }else{
            print "No new line was found and hence none was written to $target/$p\n";
        }
        close FU;

        $sub_depth=-1;
        return;
    }elsif ($f=~/fi_writefile/){#{{{fi_writefile}}}
        print "fi_writefile to write to a file $p, orig=$orig, sub_depth=$sub_depth\n" if ($debug_mode);
        if ($p=~/source=(.*);target=(.*);args=(.*)$/){
            my $gi_src=catfile($gsets->{template_dir},$gsets->{template_selected},$1);
            my $gi_tgt=$2;
            my $gi_args=$3;
            #print "source=$1\n";
            #print "target=$2\n";
            #print "args=$3\n";
            #print "gi_src=$gi_src\n";

            open(FS, '<', "$gi_src") or die $!;
            chomp(my @olines = <FS>);
            close FS;
            my @nlines=();
            #undef $gtree->{nlines};
            $gtree->{nlines}=\@nlines; # to save result lines
            #print "before processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
            __init_gtree(\@olines);
            $gtree->{file_args}=$gi_args;
            __process_file_content(\@olines);
            @nlines=@{$gtree->{nlines}};# must get it back, otherwise it might be a different one
            #print "after processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
            print "Creating $gi_tgt\n";
            open(FH, '>', "$gi_tgt") or die $!;
            foreach my $tl (@nlines){
                print FH "$tl\n";
            }
            close FH;
            implement_fo($gtree,catfile("$gi_tgt"));
            clear_fo($gtree);
            print "Complete.\n";
            #if (!defined $oldv){
            #    undef $gtree->{file_args};
            #}else{
            #    $gtree->{file_args}=$oldv;
            #}

        }else{
            print "Invalid Argument gi_writefile:$p\n";
        }
    }elsif ($f=~/get_args/){#{{{get_args}}}
        my $args=$gtree->{file_args};

        if (defined $args && length($args)>0){
            __parse_local_def($p);
            my @arr=split(/\s+/,$args);
            my @tarr=split(/\s+/,$p);
            for my $tl (0..$#tarr){
                print "loading argument $tarr[$tl] with value $arr[$tl]\n" if ($verbose_mode);
                __push_stack_vars($tarr[$tl],$arr[$tl]);
            }
        }
    }elsif ($f eq 'fo_chmod'){#{{{fo_chmod}}}
        $gtree->{file_options}->{chmod}=$p;
        return;
    }elsif ($f eq 'range'){#{{{range}}}
        if ($p=~/^\s*(\d+)\s*\.\.\s*(\d+)\s*$/){ #provide a range
            my @aar=($1..$2);
            return \@aar;
        }else{
            my @aar=split(/,/,$p);
            return \@aar;
        }
    }elsif ($f=~/\s*(\w+)\.(\w+)\s*$/){
        print("class method is called $f\n") if $debug_mode;
        my $objn=$1;
        my $mth=$2;
        return __translate_class_method($objn,$mth,$p,$orig);
    }else{
        my $hash=$sub_defs->{$f};
        if (defined $hash){
            my $ptr=$hash->{r};
            if (defined $ptr){
                print "need to pass argument to $ptr:$ptr->{var} and run\n" if ($debug_mode3);
                my @nlines=();
                my $olines=$ptr->{raw_lines};
                my $old_gtree=$gtree;
                my $curr_tree=$gtree->{curr_tree};
                my $curr_node=$gtree->{current_node};
                my $sub=$gtree->{nodes}->{$curr_node};
                $gtree={};
                $gtree->{nlines}=\@nlines; # to save result lines
                __init_gtree($olines);
                foreach my $tline (@{$olines}){
                  __explore_file_line($tline);
                  $___prev_tl=$tline;
                }
                my @argdefs=@{$ptr->{arglist}};
                my @args=split(/\s+/,$p);
                for my $kk (0..$#argdefs){
                    __push_stack_vars($argdefs[$kk],$args[$kk],$gtree);
                }
                __translate_tree($gtree);
                my @nlines=@{$gtree->{nlines}};
                $sub->{nodes}=$gtree->{nodes};
                $gtree=$old_gtree;
                print "about to attach the translated lines to current node of $gtree->{curr_tree},$gtree->{curr_tree}->{t                  ype}, curr_tree=$curr_tree, nid=$curr_node\n" if ($debug_mode3);
                return join ("\n",@nlines);
            }else{
                print "**** Error ! subroutine $f definition is found, but its body is invalid\n";
                return;
            }
        }
        print "**** Error ! Unknown function name $f !!!!!\n";
    }
    return "$p";
}
########################################################################################
# translate_class_method
#  proc_id : 0211
# argument :
#  purpose : translate class method calls 
#  pre     : $gtree is properly inited, $cls_def is parsed, class object is properly instantiated 
#  post    :
#  note    : 
########################################################################################
sub __translate_class_method{
    my $objn=$_[0];
    my $mth=$_[1];
    my $p=$_[2];
    my $orig=$_[3];
    print("fetching obj $objn from stack\n") if $debug_mode; 
    # find the object from stack 
    
    my ($hash,$objstack,$objsuper,$clssuper,$obj);
    
    if ($objn eq 'super'){# must inside a class instance and hence gtree is class context  
        #walk_dict($gtree,1,1,'highly suspect');
        $obj=$gtree->{super};
        if (! defined $obj){
            print("**** Error! Super class does not exist, cannot call its super.$mth method.\n");
            return "$obj.$mth";
        }
    }else{
        $obj=__fetch_stacked_vars($objn,$gtree->{curr_tree});
    }
    walk_dict($obj,1,1,"fetched class instance") if $debug_mode3 && $verbose_mode && defined $obj;
    if (!defined $obj){
        print("**** Error! Unknown object $objn, cannot call its method.\n");
        return $orig;
    }
    $hash=$obj->{methods}->{$mth};
    $objstack=$obj->{r}->{stack};
    $objsuper=$obj->{r}->{super};
    $clssuper=$obj->{r}->{superclass};
    
    #print("hash=$hash, objstack=$objstack, objsuper=$objsuper, clssuper=$clssuper\n");
    #walk_dict($obj,1,1,"obj is ");
    do{
        #print("hash=$hash, objstack=$objstack, objsuper=$objsuper\n");
        if (!defined $hash){
            last if (!defined $objsuper);
            $obj=$objsuper;
            $hash=$obj->{methods}->{$mth};
            $objstack=$obj->{r}->{stack};
            $objsuper=$obj->{r}->{super};
        }
    }while(!defined $hash);
    
    if (defined $hash){
        my $ptr=$hash->{r};
        if (defined $ptr){
            print "need to pass argument to $ptr:$ptr->{var} and run\n" if ($debug_mode3);
            my @nlines=();
            my $olines=$ptr->{raw_lines};
            my $old_gtree=$gtree;
            my $curr_tree=$gtree->{curr_tree};
            my $curr_node=$gtree->{current_node};
            my $sub=$gtree->{nodes}->{$curr_node};
            $gtree={};
            $gtree->{nlines}=\@nlines; # to save result lines
            __init_gtree($olines);
            $gtree->{stack}=$objstack; # the stack should be copied for class object instance 
            $gtree->{type2}=$obj->{type2};
            $gtree->{super}=$objsuper if defined $objsuper;
            walk_dict($gtree->{super},1,1,"super here is ") if $debug_mode;
            foreach my $tline (@{$olines}){
              __explore_file_line($tline);
              $___prev_tl=$tline;
            }
            my @argdefs=@{$ptr->{arglist}};
            my @args=split(/\s+/,$p);
            for my $kk (0..$#argdefs){
                __push_stack_vars($argdefs[$kk],$args[$kk],$gtree);
            }
            __translate_tree($gtree);
            my @nlines=@{$gtree->{nlines}};
            $sub->{nodes}=$gtree->{nodes};
            $gtree=$old_gtree;
            print "about to attach the translated lines to current node of $gtree->{curr_tree},$gtree->{curr_tree}->{type}, curr_tree=$curr_tree, nid=$curr_node\n" if ($debug_mode3);
            return join ("\n",@nlines);
        }
    }else{
        print("**** Error ! Unknown method $mth for $objn\n");
    }
}
########################################################################################
# instantiate_cls 
#  proc_id : 0212
# argument :
#  purpose : instantiate a new object as specified by class name 
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it 
#  post    :
#  note    : 
########################################################################################
sub __instantiate_cls{
    my $seeker=$_[0];
    my $clsdef=$cls_defs->{$seeker};
    $clsdef->{classname}=$seeker;
    print ("clsdef of $seeker is $clsdef\n") if $debug_mode;
    if (defined $clsdef){
        walk_dict($clsdef,1,1,"found class def") if ($debug_mode);
        __trace_ancester_cls($clsdef);
        my $obj=dclone($clsdef);
        print("class def is $clsdef, instantiated obj is $obj\n") if ($debug_mode);
        walk_dict($obj,1,1,"found class def") if ($debug_mode);
        return $obj;
    }
}
########################################################################################
# trace_ancester_cls 
#  proc_id : 0213
# argument :
#  purpose : worker subroutine for instantiate_cls to trace all super classes  
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it 
#  post    :
#  note    : 
########################################################################################
sub __trace_ancester_cls{
    my $seeker=$_[0];
    my $superclsn=$seeker->{r}->{superclass};
    return $seeker if ! defined $superclsn;
    my $supercls=$cls_defs->{$superclsn};
    if (! defined $supercls){
        print("**** Error ! cannot inherit superclass $superclsn for $seeker\n");
    }
    __trace_ancester_cls($supercls);
    $seeker->{r}->{super}=$supercls;
    return $seeker;
}
########################################################################################
# set_class_obj_stack_var  
#  proc_id : 0214
# argument :
#  purpose : assign value to object property   
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it 
#  post    :
#  note    : 
########################################################################################
sub __set_class_obj_stack_var{
    my $obj=$_[0];
    my $vname=$_[1];
    my $value=$_[2];    
    my $objstack=$obj->{r}->{stack};
    $objstack->{$vname}=$value;
}
########################################################################################
# set_class_obj_stack_var  
#  proc_id : 0215
# argument :
#  purpose : retrieve value to object property   
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it 
#  post    :
#  note    : 
########################################################################################
sub __get_class_obj_stack_var{
}
########################################################################################
# parse_local_def
#  proc_id : 0220
# argument :
#  purpose : parse {{{define ....}}} function, and extract array definition and those with intial values
#  pre     : $gtree is properly inited
#  post    :
#  note    : currently only process array intial values
########################################################################################
sub __parse_local_def{
    my $f=$_[0];
    print "Parsing local def $f\n" if ($debug_mode);
    if ($f=~/^(.*)\s*(^|\,|\s)(\w+)\s*\=\s*(\(([a-zA-Z][\w|\,]*)\))(.*)$/){ # try find array definition
        print "Find Array definition s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6\n" if ($debug_mode && $verbose_mode);
        my $h=$1;
        my $t=$6;
        my $var=$3;
        my $c=$5;
        my @arr=split(/\,/,$c);
        print "gtree is $gtree\n" if ($debug_mode);
        print "gtree->curr_tree is $gtree->{curr_tree}\n" if ($debug_mode);
        print "inited array length is ". scalar @arr . "\n" if ($debug_mode);
        print "pushing array $var into stack \n" if ($debug_mode);

        if (! defined $gtree->{curr_tree} || $gtree->{curr_tree}==$gtree){
            $gtree->{stack}->{$var}=\@arr;
        }else{
            $gtree->{curr_tree}->{stack}->{$var}=\@arr;
        }
    }elsif ($f=~ /^\s*(\w+)(\s+$|\s*$|\s*=\s*(.*)$)/){# literal or no value , push to stack 
        my $var=$1;
        my $rem=$3;
        print "gtree is $gtree\n" if ($debug_mode);
        print "gtree->curr_tree is $gtree->{curr_tree}\n" if ($debug_mode);
        print "pushing variable $var into stack \n" if ($debug_mode);
        if (! defined $gtree->{curr_tree} || $gtree->{curr_tree}==$gtree){
            $gtree->{stack}->{$var}=$rem;
        }else{
            $gtree->{curr_tree}->{stack}->{$var}=$rem;
        }        
    }elsif ($f=~ /^\s*(\w+)\s+as\s+(\w+)$/){# class definition, instantiate and push to stack 
        my $var=$1;
        my $clsdef=$2;
        print "gtree is $gtree\n" if ($debug_mode);
        print "gtree->curr_tree is $gtree->{curr_tree}\n" if ($debug_mode);
        print "instantiate class object $var as $clsdef\n" if ($debug_mode); 
        print "pushing variable $var into stack \n" if ($debug_mode);
        my $obj=__instantiate_cls($clsdef);
        if (! defined $obj){
            print ("**** Error ! Unknowns class $clsdef, cannot instantiate\n");
        }
        if (! defined $gtree->{curr_tree} || $gtree->{curr_tree}==$gtree){
            $gtree->{stack}->{$var}=$obj;
        }else{
            $gtree->{curr_tree}->{stack}->{$var}=$obj;
        }        
    }
}

########################################################################################
# push_local_hash_def
#  proc_id : 0230
# argument :
#  purpose : parse {{{push_hash ....}}} function, and extract hash definition
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
sub __push_local_hash_def{
    my $p=$_[0];
    if ($p=~/\s*(\w+)\s+(\w+)\s+(.+)$/){
        my $hash=$1;
        my $key=$2;
        my $rv=$3;
        print "pushing value $rv with key=$key to $hash\n" if ($debug_mode || $debug_mode2);
        if ($rv=~/^\s*\(([\s|\w|\,]+)\)\s*$/){ # pushing array
            my $dv=$1;
            my @dv=split(/\,/,$dv);
            print "about to push data into $hash with $dv\n" if ($debug_mode);
            my $tree;
            if (! defined $gtree->{curr_tree} || $gtree->{curr_tree}==$gtree){
                $tree=$gtree;
            }else{
                $tree=$gtree->{curr_tree};
            }
            return if (! defined $tree);
            my $hashref=$tree->{stack}->{$hash};
            if (!defined $hashref){
                $tree->{stack}->{$hash}->{$key}=\@dv;
            }else{
                $hashref->{$key}=\@dv;
            }
            print "hashref is located , $hashref, data is pushed : ". scalar @dv . "\n" if ($debug_mode && $verbose_mode);
        }else{
        }
    }else{
        return "Invalid function call: $p\n";
    }
}
########################################################################################
# parse_var_assignment
#  proc_id : 0240
# argument :
#  purpose : parse {{{push_hash ....}}} function, and extract hash definition
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
sub __parse_var_assignment{
    my $f=$_[0];
    print "Parsing var assignment statement $f\n" if ($debug_mode);
    if ($f =~ /^\s*(\S+)\s*=(.+)$/){
        my $vname=$1;
        my $value=$2;
        $value=~s/^\s+|\s+$//g;
        if ($value=~/{{{|}}}|###|<<<|>>>/){
            $value=__translate_stacked_vars($value);
            $value=__substitute_string($value);
        }
        
        if ($vname=~/^\s*(\w+)\.(\w+)\s*$/){
            my $objn=$1;
            my $vname=$2;
            print("found object assignment statement for $objn\n") if $debug_mode;
            print("fetching obj $objn from stack\n") if $debug_mode; 
            # find the object from stack 
            my $obj=__fetch_stacked_vars($objn,$gtree->{curr_tree});
            walk_dict($obj,1,1,"fetched class instance") if $debug_mode3 && $verbose_mode && defined $obj;
            if (!defined $obj){
                print("**** Error! Unknown object $objn, cannot call its method.\n");
                return $f;
            }
            __set_class_obj_stack_var($obj,$vname,$value);
        }else{
            print "pushing stack var $vname=$value\n" if ($debug_mode);
            __push_stack_vars($vname,$value);
        }
        
    }else{
        print "**** Error ! Invalid assign statement : $f\n";
    }
}
########################################################################################
# parse_var_retrieval
#  proc_id : 0241
# argument :
#  purpose : parse variable retrieval if is has any dynamic part 
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
sub __parse_var_retrieval{
    my $f=$_[0];
    print "Parsing var get statement $f\n" if ($debug_mode);
    if ($f =~ /^(.+)$/){
        my $vname=$1;
        my $max=100;
        ## keep translate until it is all drained out 
        while ($vname=~/{{{|}}}|###|<<<|>>>/ && $max>0){
            $vname=__translate_stacked_vars($vname);
            $vname=__substitute_string($vname);
            $max--;
        }       
        if ($vname=~/^\s*(\w+)\.(\w+)\s*$/){
            my $objn=$1;
            my $vname=$2;
            print("found object assignment statement for $objn\n") if $debug_mode;
            print("fetching obj $objn from stack\n") if $debug_mode; 
            # find the object from stack 
            my $obj=__fetch_stacked_vars($objn,$gtree->{curr_tree});
            walk_dict($obj,1,1,"fetched class instance") if $debug_mode3 && $verbose_mode && defined $obj;
            if (!defined $obj){
                print("**** Error! Unknown object $objn, cannot call its method.\n");
                return $f;
            }
            __get_class_obj_stack_var($obj,$vname);
        }else{
            return __fetch_stacked_vars($vname);
        }
    }else{
        print "**** Error ! Invalid get statement : $f\n";
    }
}
######### utility rubroutines ####################
sub __find_nested_pairs{
    my $s=$_[0];
    my $e=$_[1];
    my $hash=$_[2];
    my $idx=$hash->{nodeidx};
    
    return "" if !defined $hash;
    
    return $hash->{str} if $hash->{status} eq 'close' || $hash->{status} eq 'error';
    
    my $hstr='^(((?!'.$s.').)*)'.$s.'(.*)$';
    my $tstr='^(((?!'.$e.').)*)'.$e.'(.*)$';
    
    my $h;
    my $t;
    my $str1=$hash->{str};
    
    return '' if length($str1)==0;
    
    if ($hash->{status} eq 'idle'){
        if ($str1=~/\E$hstr/){
            print("s1=$1, s2=$2, s3=$3, s4=$4, s5=$5, s6=$6\n") if ($debug_mode && $verbose_mode);
            my $h=$1;
            my $t=$3;        
            if (length($h)>0 && index($h,$e)>=0){ # invalid , unmatched pair 
                $hash->{status}='error';
                $hash->{message}="found \"$e\", but no \"$s\" matches it.";
                $hash->{break}=$str1;
            }else{
                if (defined $h && length($h)>0){
                    $idx++;
                    my $hash1;
                    $hash1->{type}='p'; # plain line 
                    $hash1->{str}=$h;
                    $hash->{nodes}->{$idx}=$hash1;
                }
                
                if (length($t)==0){ # done 
                    $hash->{status}='error';
                    $hash->{message}="missing closing \"$e\" in  $str1.";
                    $hash->{break}=$h;
                    return '';
                }
                
                $idx++;
                my $hash2;
                $hash2->{type}='m'; # matching 
                $hash2->{str}=$t;
                $hash2->{status}='open';
                $hash->{nodes}->{$idx}=$hash2;
                
                my $e2=__find_nested_pairs($s,$e,$hash2);
                
                if ($hash2->{status} eq 'open'){
                    $hash->{status}='error';
                    $hash->{message}="missing \"$e\"";
                    $hash->{break}=$str1;        
                    return $e2;
                }elsif ($hash2->{status} eq 'error'){
                    $hash->{status}='error';
                    $hash->{message}=$hash2->{message};
                    $hash->{break}=$str1;
                    return '';
                }elsif (defined $e2 && length($e2)>0){ # continue checking
                    $hash->{str}=$e2;
                    $hash->{status}='idle';
                    return __find_nested_pairs($s,$e,$hash);
                }
                
                $hash->{status}='close';
                $hash->{str}='';
                return '';
            }
        }elsif (index($str1,$e)>0){
            $hash->{status}='error';
            $hash->{message}="found \"$e\", but no \"$s\" matches it.";
            $hash->{break}=$str1;
            return '';            
        }else{
            $idx++;
            my $hash1;
            $hash1->{type}='p'; # plain line 
            $hash1->{str}=$str1;
            $hash->{nodes}->{$idx}=$hash1;        
        }
    }elsif ($hash->{status} eq 'open'){
        if ($str1=~/\E$tstr/){
            print("s1=$1, s2=$2, s3=$3, s4=$4, s5=$5, s6=$6\n") if ($debug_mode && $verbose_mode);
            my $h=$1;
            my $t=$3;                
            if (length($h)>0 && index($h,$s)>=0){ # possible a nested pair
                $h=substr($h,0,index($h,$s));
                $idx++;
                my $hash1;
                $hash1->{type}='p'; # plain line 
                $hash1->{str}=$h;
                $hash->{nodes}->{$idx}=$hash1;
                $t=substr($str1,index($h,$s));
                
                if (length($t)<=0){
                    $hash->{status}='error';
                    $hash->{message}="missing \"$e\"";
                    $hash->{break}=$str1;        
                    return '';
                }
                
                $idx++;
                my $hash2;
                $hash2->{type}='m'; # matching 
                $hash2->{str}=$t;
                $hash2->{status}='open';
                $hash->{nodes}->{$idx}=$hash2;
                my $e2=__find_nested_pairs($s,$e,$hash2);

                if ($hash2->{status} eq 'open'){
                    $hash->{status}='error';
                    $hash->{message}="missing \"$e\"";
                    $hash->{break}=$str1;        
                    return $e2;
                }elsif ($hash2->{status} eq 'error'){
                    $hash->{status}='error';
                    $hash->{message}=$hash2->{message};
                    $hash->{break}=$str1;
                    return '';
                }elsif (defined $e2 && length($e2)>0){ # continue checking
                    $hash->{str}=$e2;
                    $hash->{status}='idle';
                    return __find_nested_pairs($s,$e,$hash);
                }
                
                $hash->{status}='close';
                $hash->{str}='';
                return '';
            }
        }else{
            $hash->{status}='error';
            $hash->{message}="missing \"$e\"";
            $hash->{break}=$str1;
            return '';
        }
    }
}
sub __find_match{
    my $s=$_[0];
    my $e=$_[1];
    my $str=$_[2];
    print "str=$str s=$s,e=$e\n" if ($debug_mode && $verbose_mode);
    my $pos1=index($str,$s);
    my $pos2=index($str,$e);
    #print "pos1=$pos1, pos2=$pos2\n";
    if ($pos2==-1){# not found 
        return -1;
    }elsif ($pos1==-1){
        return $pos2;
    }elsif ($pos1>=$pos2){
        return $pos2;
    }else{
        return $pos2+length($e)+__find_match($s,$e,substr($str,$pos2+length($e)));
    }
}
sub __find_first_collection{
    my $str=$_[0];
    
    print "__find_first_collection arg1:$str\n" if ($debug_mode && $verbose_mode);
   
    my $pos1= index($str,'{{{');
    my $pos2= index($str,'<<<');
 

    if ($pos1>=0 && $pos1<$pos2){
        if ($str=~/(((?!\{\{\{).)*)\{\{\{(((?!\}\}\}).)*)\}\}\}(.*)/){
            print "type=func,s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7\n" if ($debug_mode);
            my $h=$1;
            my $c=$3;
            my $t=$5;        
            return (length($h),'h',$c,$t);
        }
    }else{
        if ($str=~/(((?!<<<).)*)<<<(((?!>>>).)*)>>>(.*)/){
            print "type=s,s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6,s7=$7\n" if ($debug_mode);
            my $h=$1;
            my $c=$3;
            my $t=$5;
            return (length($h),'s',$c,$t);
        }
    }
}

sub set_global_hash{
    my $k=$_[0];
    return unless defined $k;
    $app_params=dclone $k;
}
sub get_global_hash{
    return $app_params;
}
sub is_muted{
    my $key=$_[0];
    my $h=$muted_params->{$key};
    return 1 if $h;
    return 0;
}
sub pad_s{
    my @params=@_;    
    my $len=$params[0];
    my $output='';
    
    if ( scalar @params <=1 ) {
        return @params;
    }else{
        for my $tl (1..$#params){
            $output.="$params[$tl] ";
        }
        $output=~ s/\s+$//;
        my $len2=length($output);
        return $output.' ' x ($len - $len2);
    }
}
sub pad_t{
    my @params=@_;    
    my $h=pad_string(@params);
    
   if ( scalar @params <=1 ) {
        return @params;
   }else{
        my $len=$params[0];
        my $len2=length($h);
        my $rem=$len-$len2;
        my $id1=1;
        my $id2=$#params;
        my $a1=0;
        my $a2=0;
        my $h1='';
        my $h2='';
        
        #print "rem=$rem\n";
        while ($a2<=$rem){
           $h2.=$h1;
           $a2=length($h2);
           $h1=$params[$id1++];
           $a1=length($h1);
           $a2+=$a1;
           #print "h1=$h1,h2=$h2,a1=$a1,a2=$a2\n";
           last if ($a1==0 || $id2>$id1); 
           $h1.=" ";
        }
        $h2=~ s/\s+$//g;
        return $h."$h2".' ' x ($len - $len2 - length($h2));
    }
}

sub pad_string{
   my (@params)=@_;
  
   if ( scalar @params <=1 ) {
        return @params;
   }else{
        my $len=$params[0];
        my ($rem,$cnt,$len2);
        my $tts='';
        my $mx=$#params;
        for my $idx (1..$#params){
            $tts.=$params[$idx];
            $tts.=' ' unless ($mx ==1);
        }
        $len2=length($tts);
        $cnt=floor($len/$len2);
        $rem=$len-$cnt*$len2;
        return $tts x $cnt;
   }   
}

sub reval_expr{
    my $confined_code=$_[0];
    my $result = $compartment->reval($confined_code);
    print "result=$result in reval_expr\n" if ($debug_mode && $verbose_mode);
    return $result;
}

sub split_q{
    my $delim=$_[0];
    my $strr=$_[1];
    my $keep_quote=$_[2];
    $keep_quote=0 if ! defined $keep_quote;
    my ($h,$c,$t);
    
    print(">> split_q : delim=$delim, strr=$strr, keep_quote=$keep_quote\n") if $debug_mode;
    
    if ($strr=~/^([^\"]*)\"([^\"]*)\"(.*)$/){
    # contains string with double-quoations 
        $h=$1; $c=$2; $t=$3;
    }else{
        return split($delim,$strr) 
    }

    my $re='^\s*'.$delim.'(.*)$';
    
    if ($t=~/\E$re/){
        $t=$1;
    }
    my @arr1;
    my @arr2;
    my $len1;
    my $len2;
    
    $c="\"".$c."\"" if ($keep_quote); 
    
    $re="(.+)".$delim."(((?!".$delim.").)*)";
    if ($h=~/\E$re/){
    # if leadning substring contains non-empty script after last delimiter
        $c=$2.$c;
        $h=$1;
        if (defined $h){
            @arr1=split($delim,$h);
            $len1=scalar @arr1;
            @arr1=(@arr1,($c));
        }else{
            @arr1=($c)
        }
    }else{
        @arr1=split($delim,$h);
        $len1=scalar @arr1;
        if ($len1==0){
            @arr1=($c);
        }elsif ($len1==1){
            @arr1=(@arr1[0].$c);
        }elsif ($len1==2){
            @arr1=((@arr1[0]),(@arr1[1].$c));
        }else{
            @arr1=(@arr1[0..($len1-2)],(@arr1[$len1-1].$c));
        }
    }
    
    return @arr1 if (! defined $t);
    
    @arr2=split_q($delim,$t,$keep_quote);
    
    print("!!!!!!!!!!!!!!!!!!! t=$t  arr2=@arr2\n") if $debug_mode;
    
    $len1=scalar @arr1;
    $len2=scalar @arr2;
    
    return @arr1 if $len2==0; 
    return @arr2 if $len1==0; 
    
    return (@arr1,@arr2); 
}

######### miscellaneous subroutines ##############
########################################################################################
# print_params
#  purpose : print out all parameters detected in template files 
#  pre     : parse_template & __get_variable_values are both called
#  post    : program is ready to call __process_template subroutine  
########################################################################################
sub __print_params{
    my $p=@_[0];
    my $wid=$preview_banner_width;
    my $head="+"."-"x ($wid-2) . "+";
    print "$head\n";
    
    if ($p eq 'raw'){
        foreach my $k (sort keys %{$raw_params}){
            print "| ".pad_s(($wid-4),$k,": $app_params->{$k}")." |\n";
        }
    }elsif ($p eq 'muted'){
        foreach my $k (sort keys %{$muted_params}){
            print "| ".pad_s(($wid-4),$k,": $muted_params->{$k}")." |\n";
        }        
    }else{
        foreach my $k (sort keys %{$app_params}){
            print "| ".pad_s(($wid-4),$k,": $app_params->{$k}")." |\n";
        }
    }
    print "$head\n";
}

########################################################################################
# print_gtree
#  purpose : debug, print out all branches and leaves in gtree 
#  pre     : 
#  post    : no,this sub is to look into the content of gtree  
########################################################################################
sub print_gtree{
    my $ct=$_[0];
    print "Printing tree $ct...\n" if ($debug_mode2);

    if (defined $ct){
        my $nodes=$ct->{nodes};
        if (defined $nodes){
            my $level=$ct->{level};
            my $pstr=pad_t($level+2,'-');
            foreach my $k ( sort { $a <=> $b } keys %{$nodes}){
                if ($nodes->{$k}->{t} eq 'p'){
                    print $pstr. " $k. " . $nodes->{$k}->{s}."t=$nodes->{$k}->{t}\n";
                }else{
                    my $sub=$nodes->{$k}->{r};
                    if (defined $sub){
                        ## dig into sub nodes     
                        print $pstr. "Drill into sub nodes $sub...\n" if ($debug_mode2);
                        if ($sub->{t} eq 'f'){
                            print $pstr. "This is a foreach loop against $sub->{list}, var is $sub->{var} ...\n" if ($debug_mode2);
                        }
                        print_gtree($sub);
                    }else{
                        print "Something is wrong, r is defined in $sub->{r}\n" if ($debug_mode2);
                    }
                }
            }
        }
    }    
}

########################################################################################
# exit_when_not_found
#  purpose : exit when file not found  
#  pre     : 
#  post    : 
########################################################################################
sub exit_when_not_found{
    my $fn=@_[0];
    my $opt=@_[1];
    
    if (! -e $fn){
        print "!!!! Error , $fn does not exist.\n";
        return 1 if ($opt == 1);
        exit 0;
    }
    return 0;
}
########################################################################################
# walk_dict
#  purpose : walk and print content of a hash reference   
#  pre     : 
#  post    : 
########################################################################################
sub walk_dict{
    my $d=$_[0];
    my $depth=$_[1];
    my $hide_list=$_[2];
    my $title=$_[3];
    my $touch_count=$_[4];
    $touch_count={} if ! defined $touch_count;    
    if (defined $touch_count->{$d}) {
        $touch_count->{$d}=$touch_count->{$d}+1;
    }else{
        $touch_count->{$d}=1;
    }
    $depth=0 if ! defined $depth;
    $hide_list=1 if ! defined $hide_list;
    my $head='';
    if (defined $title ){
        my $wid=$preview_banner_width;
        $head="+"."-" x ($wid-2) . "+";
        print("$head\n");
        print("| ".pad_s($wid-4,$title)." |\n");
        print("$head\n");
    }
    if (! defined $d){
        print("  " x $depth . " None \n");
        return;
    }elsif ($touch_count->{$d}>=3){
        print("  " x $depth . " $d was referenced earlier, stop drilling.\n");
        return;        
    }   
    foreach my $k (sort keys %{$d}){
        my $v=$d->{$k};
        if (ref $v eq 'HASH'){
            print("  " x $depth . "+[ $k ]\n");
            print("  " x $depth . "+[ ref : $v ]\n") if ($show_ref_while_walking);    
            if ($k eq 'parent' && $hide_parent_while_walking){
                print("  " x ($depth+1) . "+[ ref : $v ]\n") if (!$show_ref_while_walking);    
            }else{            
                walk_dict($v,$depth+1,0,undef,$touch_count);        
            }
        }else{
            if ($hide_list && ref $v eq 'ARRAY'){
                print("  " x $depth . " [ $k ] = [ ".(scalar $v)." elements ]\n"); 
            }else{    
                print("  " x $depth . " [ $k ] = [ $v ]\n");
            }
        }
    }  
    print("$head\n") if (defined $title);
}
