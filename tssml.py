#**********************************************************************************************************************************
# Package Name: tssml - Template Substitution Script Language
#        Usage: It is to implement TSSML in processing text template files
#         Note:
#      Version: 2.0 -- Jan, 21, 2021
#      Author : Guangyu Yang
#        Note : migrated from Perl implementation , tssml.pm 1.2
#       **** new migration in progress, trying to catch up with tssml.pm 1.2.1 ***
#       **** below are the features to catch on *******
# >>>>>>>> progress
#   >>>>>> checking main functions
#
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
#     7. get    : retrieve a value with dyanmic parts
#     8. push_hash : push value to hashtable
#     9. iif    : inline if condition
#    10. expr   : evaluate expression
#    11. hash_keys : get keys of a hash
#    12. flat_list_f : convert array elements or hash keys into one line and optionally call a function to preprocess each element before merge to a list
#    13,14,15. sub_l,sub_r, sub_m   : substring functions
#    16,17. pad_t, pad_s  : pad string to certain length with spaces
#    18,19. lc, uc : convert string to all lowercase or uppercase
#    20. wrap_lst_ :
#    21. diff_update :  compare files and only append new lines to file
#    22. fi_writefile :  parameterize the file names to be iterated and generated respectively
#    23. fo_chmod :
#    27. range :  create array based on range of numbers or string list
#    25. get_args
#    26. contains : check exisitence of array or hash elements
#    27. fields :  get fields from a string with delimiter defined
### notes
#    subroutines are the ones used in this package to implement tssml
#    tssml functions are those used in templates as part of tssml
#**********************************************************************************************************************************
import sys, os, os.path, socket, platform,re,copy,math,shlex,random,datetime
from os import path
from os import walk
from copy import deepcopy
from math import floor
from math import ceil
#internal variables
__inited=0
debug_mode=1
debug_mode2=1
debug_mode3=1
debug_mode4=1
verbose_mode=1

__debug_flag=''
sub_depth=0
__loop_lmt=1000000 # threshold for loop to avoid dead loop
___prev_tl=None
additional_params_file=".___additional_template_vars_menusetup"

gtree={}  # parsing tree for each file
gsets={} # global setting
gsets['param_file']=additional_params_file
gsets['template_dir'] = os.path.dirname(os.path.abspath(sys.argv[0]))
gsets['cwd']=os.getcwd()
#####################################
# eval is safe in python
# not like python which needs to use safe compartment
#####################################
## global variables in hashtable

preview_banner_width=56
app_params={}  ## variables that has values provided in anyway
raw_params={}  ## variables that has not yet provided values
ref_params={}  ## map from stacked variable to global substitution variable <name> to <name> , not actual reference
muted_params={} ## variables that are muted -- in other words, won't prompt for input
sub_defs={}    ## definition of subroutine
arr_refs={}    ## array reference box
cls_defs={};   ##+? class definition, global
######################################################################
# temporary ref for dictionary object being accessed in function
######################################################################
__cached_dict__={}
__cached_assign=None
####################################################
# internal subroutines  im: 4 out of 4, plus 6 new
def init_settings() :
    if not __inited :
        reinit_settings()
    return
#im:n1
def reinit_settings() :
    __get_hostname()
    __inited=1
    return
def __get_hostname() :
    gsets['hostname']=socket.gethostname()
    gsets['fqdn']=socket.getfqdn()
    gsets['os_type']=platform.system()
    return
#im:n2
def __print_gsets() :
    walk_dict(gsets)
#im:n3
def __print_gtree() :
    head="+"+ ("-" * (preview_banner_width-2)) +"+"
    print(head)
    print("| "+pad_s([preview_banner_width-4,"gtree content --->"])+" |")
    print(head)
    walk_dict(gtree)
    print(head)
#im:n4: because python does not print object reference#
def get_tree_by_tnid(tnid) :
    return __get_tree_by_tnid(tnid)
#im:n5: because python does not print object reference#
def __get_tree_by_tnid(tnid) :
    #print("--->get_tree_by_tnid="+tnid)
    if tnid==None : return gtree
    arr=re.split('-',tnid)
    #print(*arr)
    sub=gtree
    idx=0
    #print(sub)
    for a in arr:
        #print("a="+a)
        if a=='0' : continue
        else      : sub=sub['nodes'][int(a)]['r']
    return sub
#im:n6:
def __curr_tree() :
    tnid=gtree['tnid']
    return __get_tree_by_tnid(tnid)
def __init_gtree(ola=None) :
    onum= (0 if ola==None else len(ola))
    global gtree # declare its global ,otherwise, below initialization makes it local
    gtree={}
    gtree['current_level']=0
    gtree['current_line']=0
    gtree['current_node']=0
    # because Python does not support reference
    # as workaround , use tree-node-id to identify + locate tree node when parsing/processing tree
    # tnid is a list , each element indicates which node it is in its level
    # for example:
    ##########################################################
    # 0 means tree-node itself , 1+ means children
    # [0] root                        [gtree]
    # [1] root-> p                        Hello World
    # [2] root-> p                        {{{set j=100}}}
    # [3] root-> while                    {{{while {{{expr ###j###<100}}}
    # [3,1] root->while->case                   {{{case
    # [3,1,1] root->while->case->ccctrl               [ctrl node]
    # [3,1,1,1] root->while->case->ccctrl->when            {{{when {{{expr ###j###<1000}}} then
    # [3,1,1,1,1] root->while->case->ccctrl->when->p           Item amount [###j###] is at low level, need to get some.
    # [3,1,1,1,2] root->while->case->ccctrl->when->p           Please contact vendor@abc.com for quote.
    # [None] -- to be skipped                              when}}}
    # [3,1,1,2] root->while->case->ccctrl->when            {{{when {{{expr ###j###<10000}}} then
    # [3,1,1,2,1] root->while->case->ccctrl->when->p           Item amount [###j###] is at medium level, no action is required.
    # [None] -- to be skipped                              when}}}
    # [3,1,1,3] root->while->case->ccctrl->when/else       {{{else then
    # [3,1,1,3,1] root->while->case->ccctrl->when->p           Item amount [###j###] is suffcient, no concerns for now.
    # [None] -- to be skipped                              when}}}
    # [None] -- to be skipped                         case}}}
    # [3,2] root->while                         Above information is provided by system.
    # [None] to be skipped                while}}}
    # [4] root->p                         Below are the list of databases on the system
    # [5] root->foreach                   {{{foreach i in {{{hash_keys <<<CDB_PDB_HASH>>>
    # [5,1] root->foreach-> p                 {{{escape_var_g<<<<<<<<<<<<<<<< CDB = ###i### >>>>>>>>>>>>>>>>>>>>>>>>>>}}}
    # [5,2] root->foreach->foreach            {{{foreach k in {{{get_hash_value <<<CDB_PDB_HASH>>> ###i### pdb_list}}}
    # [5,2,1] root->foreach->foreach->p           +-------------------------------------------------------+
    # [5,2,2] root->foreach->foreach->p           | pad_s(48,PDB : ###k### ) |
    # [5,2,3] root->foreach->foreach->p           +-------------------------------------------------------+
    # [None] to be skipped                    foreach}}}
    # [None] to be skipped               foreach}}}
    # [6] root->p                        All information is provide
    # [7] root->p                        <<<<<<<<<<<<<<<<<<<<<< End of Information
    gtree['level']=0
    #####################################
    # gtree->curr_tree
    # the node that currently being parsed , implementation by languages use object reference, but python does not support reference
    # this might induce some issues, instead, tnid is recording the chain of branching nodes
    # curr_tree & tnid are needed only for
    gtree['curr_tree']=None
    gtree['tnid']='0'
    gtree['curr_tnid']='0'
    gtree['parent_tnid']=None
    #####################################
    gtree['source']=ola         # original lines before processing
    gtree['total_lines']=onum   # will be removed
    gtree['nlines']=[]          # to save result lines after processing
    gtree['status']='open'      # 0=idle
    gtree['type']='root'        # root tree
    gtree['stack']={}           # variable stack
def set_debug_flag(cl) :
    if cl=="--debug" : debug_mode=1
    if cl=="--verbose" : verbose_mode=1
    if cl=="--debug2" : debug_mode2=1
    if cl=="--debug3" : debug_mode3=1
    if cl=="--debug4" : debug_mode4=1

#################################################################################
# g_start_interactive
#   proc_id : 0010
#   purpose : Entry point which will run whole module interactively
# arguments : template_directory (optional)
#      pre  : if the caller script is not in the parent directory of templates,
#                call set template_dir first to tell the package where the templates are
#             otherwise, no mandatory preliminary steps
#     post  : optionally, inherit get_customized_values in main program
#     updat :
#            comparing to Perl, this function in Python needs to split into multiple steps
#            check the def below for TSSMLDriver, which shows how it works
#################################################################################
def g1_start_interactive(tpl_dir):
    global gsets
    global gtree
    init_settings()
    if tpl_dir != None and path.isdir(tpl_dir) :
        gsets['template_dir']=tpl_dir
    else:
        tpl_dir=gsets['template_dir']

    #print("tpl_dir="+tpl_dir)

    print("current working directory is "+gsets['cwd'])
    print("script directory is " + gsets['template_dir'])
    print("")

    template_arr = [f for f in os.listdir(tpl_dir) if os.path.isdir(os.path.join(tpl_dir, f)) and re.match("^[^_]",f)]

    if (len(template_arr) <= 0) :
        print("*** Error ! no template exists under " + tpl_dir +" ***")
        quit()

    print("Available Templates under "+tpl_dir+" :")
    idx=1
    for tl in template_arr:
        print(" "+str(idx)+"."+tl)
        idx+=1

    print("Select Template[ " + template_arr[0] + " ]:")
    template=sys.stdin.readline()
    template=chomp(template)
    if re.match("^\s*\Z",template) :
        template=template_arr[0]
    print("*** template is " + template)
    gsets['template_selected']=template

    print("Select Target Directory [" + gsets['cwd'] +":")
    target=sys.stdin.readline()
    target=chomp(target)
    if re.match("^\s*\Z",target) :
        target=gsets['cwd']
    print("*** target directory is "+target)
    gsets['target']=target
    if target == path.join(tpl_dir,template) :
        print("*** Error *** You are going to write files to template directory!\n That would destory template, you must change to different target directory.\n")
        quit()
    __parse_template(template)
    print ("Getting values for substitution variables detected in template...")
    return
def g2_start_interactive():
    __get_variable_values()
    __print_preview()
##############################################################
# Control class for user to call
# it is wrapper class for global functions and variables here
##############################################################
class TSSMLDriver(): # will make it singleton soon
    # Constructor
    def __init__(self):
        self.value = "Inside Parent"
    # Parent's public methods to inherit in children
    def start_interactive(self,tpl_dir=None) :
        g1_start_interactive(tpl_dir)
        self.get_customized_values() # for child to inherit and override with customized codes
        g2_start_interactive() # continue with default behavior
    #################################################################################
    # get_customized_values
    #   proc_id : 0020
    #   purpose : define this subroutine with exact same name to inherit it.
    # arguments : none
    #      pre  : ___parse_template is called so that all substitution variables are detected
    #     post  : optionally, inherit get_customized_values in main program
    #     note  : do not modify this subroutine here
    #################################################################################
    def get_customized_values(self):# for child to inherit and override with customized codes
        pass
#########################################################################################################
# __parse_template
#   purpose : parse template to get all substitution variable names required in the templates
#   proc_id : 0030
# arguments : template name
#      pre  : this is internal routine , getparams_interactive or getparams_noninteractive calls this sub
#     post  : call get_customized_values
#     note  : Not needed to be called in your code
#########################################################################################################
def __parse_template(template) :
    dirname=gsets['template_dir']
    tl= path.join(dirname,template)
    print("Parsing template ...")

    files = [f for f in os.listdir(tl) if os.path.isfile(os.path.join(tl, f)) and not re.match("(^[\.]\s*$|^[\.\.]\s*$)",f)]
    j=0;
    for ttl in files :
        j+=1
        if ( ttl == additional_params_file ):
            print("Found additional parameter definition file: " + ttl + "in template")
            print("Extracting additional parameter definition...")
            __parse_params_def_file(os.path.join(tl,ttl))
            continue

        if debug_mode or debug_mode2 : print("Looking for variables in file " + ttl + " content")
        FS = open(os.path.join(tl, ttl), "r")
        lines=FS.readlines()
        FS.close()
        if debug_mode or debug_mode2 : print("Size of lines="+str(len(lines)))
        for fl in lines:
            __parse_template_line(fl)
            fl=fl.rstrip()
            m=re.match("^\s*{{{mute\s+(.+)\s*}}}$",fl)
            if (m) :
                ll=shlex.split(m.group(1))
                for llr in ll :
                    muted_params[llr]={'muted':'y'}
                    pass
            pass
        pass
    if (j<=0) :
        print("**** Error ! Empty template, nothing to process")
        quit()

    if verbose_mode or debug_mode :
        print("Detected below variables...")
        __print_params('raw')
#########################################################################################################
# __parse_params_def_file
#   purpose : extract substitution variables from default parameter file
#   proc_id : 0031
# arguments : default parameter file name
#      pre  : none
#     post  : none
#     note  : Not needed to be called in your code
#########################################################################################################
def __parse_params_def_file(filename) :
    global __cached_dict__
    global raw_params
    print("Parsing template default parameter file " + filename + "...")
    if debug_mode or debug_mode2 : print("Looking for variables in content of file " + filename)
    FS = open(filename, "r")
    lines=FS.readlines()
    FS.close()
    if debug_mode or debug_mode2 : print("Size of lines="+str(len(lines)))
    delim='\s+'
    for fl in lines:
        fl=fl.rstrip()
        m=re.match("^\s*#",fl)
        if (m) :
            continue
        if assign_expr(None,re.match("^\s*\!\s*(\w+)\s*(.*)$",fl)) :  # command line in parameter file
            m=get_last_assign()
            cmd,drc=m.group(1),m.group(2)
            print("cmd="+cmd+" - drc="+drc)
            if cmd== 'delim' : # delimiter command
                if assign_expr(None,re.match("^\s*(\S+)(\s*|$)",drc)) :
                    m=get_last_assign()
                    delim=m.group(1)
            continue
        if debug_mode : print("delimiter is set to "+delim)
        arr=re.split(delim,fl)
        print("Arr=",arr)
        if (arr[0]!=None and len(arr[0])>0):
            arr[0]=re.sub("(^\s+|\s+$)","",arr[0])
            if debug_mode : print("adding to raw_params", arr)
            __cached_dict__=raw_params
            set_hash_value(None,arr[0],"name",arr[0])
            if arr[1] !=None :
                __cached_dict__=raw_params
                set_hash_value(None,arr[0],"type",arr[1])
            if arr[2] !=None :
                arr[2]=re.sub("(^\s+|\s+$)","",arr[2])
                __cached_dict__=raw_params
                set_hash_value(None,arr[0],"default",arr[2])
            if (arr[3]!=None):
                __cached_dict__=raw_params
                set_hash_value(None,arr[0],"desc",arr[3])
    pass
    print(raw_params)
    walk_dict(raw_params,title="RAW PARAMETER CONTENT")
#########################################################################################################
# __parse_template_line
#   purpose : parse each line of template file to find all substitution variables
#   proc_id : 0040
# arguments : original line read from template file
#      pre  : this is internal routine , parse_template sub calls this sub
#     post  : none
#     note  : Not needed to be called in your code
#########################################################################################################
def __parse_template_line(ta) :
    if (re.match("^\s*$",ta)) : return
    if (debug_mode) : print("parsing string: "+ta)
    # this step can only detect fixed variable name
    # if variable name is dynamic, it can only be detected when process_template is called
    m=re.match("(.*)<<<(((?!>>>).)*)>>>(.*)",ta)
    if (m) :
        #print(m)
        if (debug_mode) : print(m)
        #print("matched 1=" + m.group(1) + ", 2=" +m.group(2) + ", 3=" + m.group(3)+ ", 4=" + m.group(4)+", 5="+m.group(5)+", 6="+m.group(6)+" ,7="+m.group(7)
        h,t,c=m.group(1),m.group(4),m.group(2)
        m=re.match("^\s*(\w+)\s*$",c)
        if (m) :
            c=m.group(1)
            cel=raw_params.get(c)
            if cel !=None :
                if (debug_mode or verbose_mode) :
                    print(c+" is already found. Skip.")
            else:
                if (debug_mode or verbose_mode) :
                    print("Found variable name="+c+", save to hashtable")
                raw_params[c]={'name':c}
        else:
            m=re.match("^\!(\w+.+)\s+(\w+)\s*$",c)
            if (m) :
                cmdd=m.group(1)
                varr=m.group(2)
                if debug_mode : print("Found command "+cmdd+"for substitution variable [" + varr+ "]")
                raw_params[varr]={'name':varr,'command':cmdd,'type':'hash'}
            else:
                if debug_mode2 : print(c +" is not a proper variable name. Skip")

        if (re.match("\S+",h)) : __parse_template_line(h)
        if (re.match("\S+",t)) : __parse_template_line(t)
########################################################################################
# get_variable_values, get_variable_values_with_command
#  proc_id : 0050
#  argument: none
#  purpose : 1. prompt user for each substitution variable values by the name detected in template files
#  pre     : parse_template sub is called
#  post    : print_preview or process_template will be called
########################################################################################
def __get_variable_values() :
    name,type,default,desc,templ='','','','',''
    for k,v in sorted(raw_params.items(),key=lambda x: x[0]) :
        if get_hash_value(app_params,k)==None :
            name=v.get('name')
            type=v.get('type')
            default=v.get('default')
            desc=v.get('desc')
            cmdd=v.get('command')

            (name,type,default,desc,cmdd)=replace_none_with_space((name,type,default,desc,cmdd))
            #print(f"type is {type}")

            if (debug_mode or debug_mode2) : print(k+" needs value")
            print("\n------------------------------------------------------------------")
            if (desc != None and len(desc)>0):
                print(desc)
                print("------------------------------------------------------------------")

            print(k + " has no value provided but is required in template")
            if cmdd!=None :
                rett=__get_variable_values_with_command(v);
                if (rett): continue
            if assign_expr(None,re.match("\s*list\((.*)\)",type)) :
                m=get_last_assign()
                templ=m.group(1)
                tmp_arr=re.split(",",templ)
                ii=1
                for templ in tmp_arr :
                    templ=chomp(templ)
                    print(" " + str(ii) + ". " + templ)
                    ii+=1
                print(" Pick one from the list or provide your own value otherwise will use the default value.\n Provide value for " + k + " [ " + default +" ]:")
            else:
                print(" For multiple values, use ',' as delimiter.\n Put nothing if you want to skip.\n Now, provide value for " + k + "[ " +str('' if default==None else default)+" ]:")

            templ=sys.stdin.readline()
            templ=chomp(templ);

            if re.match("\S+\,",templ) :
                if (debug_mode or debug_mode2) : print("The input is a list, convert to array")
                tmp_arr=re.split(",",templ)
                app_params[k]=tmp_arr
                print("\n*** "+k+" *** is set to "+templ+"\n")
            elif not re.match("^\s*\Z",templ) :
                app_params[k]=templ
                print("\n*** "+k+" *** is set to "+templ+"\n")
            else:
                if default !=None and re.match("\S+\,",default) :
                    tmp_arr1=re.split(",",templ)
                    app_params[k]=tmp_arr1
                    print("\n*** "+k+" *** is set to defalt value in array:"+tmp_arr1+"\n")
                else:
                    app_params[k]=default
                    print("\n*** "+k+" *** is set to defalt value : "+str(default)+"\n")

    print("")
#########################################################################################################
# __get_variable_values_with_command
#  proc_id : 0051
#  purpose : parse substitution variable with directives
#  pre     : parse_template sub is called
#  post    : print_preview or process_template will be called
########################################################################################
def __get_variable_values_with_command(v) :
    if v==None : return
    global __cached_dict__
    name=v.get('name')
    type=v.get('type')
    default=v.get('default')
    desc=v.get('desc')
    cmdd=v.get('command')
    (name,type,default,desc,cmdd)=replace_none_with_space((name,type,default,desc,cmdd))

    if assign_expr(None,re.match("^\s*hash(.*)\s*$",cmdd)) :
        m=get_last_assign()
        cmdd=m.group(1)
        print("The substitution variable requires you to follow directives to build a Hashtable.")
        if assign_expr(None,re.match("\((.+)\)",cmdd)):
            m=get_last_assign()
            cmdd=m.group(1)
            arr1=split_q(",",cmdd,1)
            if debug_mode : print("Parsing Hashtable Building Directives... ...\n"+str(arr1))

            stage_hash={}
            for akk in arr1:
                arr2=split_q(":",akk,1)
                work_hash=stage_hash
                if assign_expr(None,re.match("^(.+)(\+|\-)$",arr2[0])) :
                    m=get_last_assign()
                    kky=m.group(1)
                    flg=m.group(2)
                    arr3=kky.split(".")
                    #print("----> kky="+kky)
                    #print("----arr3="+str(arr3))
                    l_a3=len(arr3)
                    ll=0
                    for pkk in arr3:
                        __cached_dict__=work_hash
                        set_hash_value(None,pkk)
                        work_hash=work_hash[pkk]
                        if ll==l_a3-1 :
                            set_hash_value(None,pkk,"flag",flg)
                            set_hash_value(None,pkk,"cmd",arr2[1])
                            if flg=='-':
                                set_hash_value(None,pkk,"desc","will add a sub-key, named "+arr2[1]+", to the ["+kky+"]. And then ask for its value(s)")
                            elif flg=='+':
                                set_hash_value(None,pkk,"desc","will ask user to input value(s) for ["+kky+"].")
                        ll+=1
            if debug_mode:
                walk_dict(stage_hash,title="Parsing the hash directives for "+name+" ....")

        __cached_dict__=app_params
        __traverse_staging_hash(stage_hash,name)
        return 1
#########################################################################################################
# __traverse_staging_hash
#  proc_id : 0052
#  purpose : based on hash directives for substitution variable, prompt user for inputs
#  pre     : parse_template sub is called, __get_variable_values_with_command is called
#  post    : print_preview or process_template will be called
########################################################################################
def __traverse_staging_hash(hash,varname,parent_name=None):
    global __cached_dict__
    target_hash=__cached_dict__

    if debug_mode : print("Get inputs for "+varname+ ("" if parent_name==None else " of "+parent_name)+" ..." )
    __cached_dict__=target_hash
    set_hash_value(None,varname)
    target_hash=target_hash[varname]

    children=None
    for k,v in sorted(hash.items(),key=lambda x: x[0]):
        if not isinstance(v,dict): continue
        flg=v['flag']
        cmd=v['cmd']
        desc=v['desc']
        arr1=[]
        if flg=='+' :
            llt=len(cmd)+2
            if parent_name ==None :
                print(f"        +"+('-'*llt)+"+")
                print(f"Provide | {cmd} | >")
                print(f"        +"+('-'*llt)+"+")
            else:
                llt+=len(parent_name)+4
                print(f"        +"+('-'*llt)+"+")
                print(f"Provide | {cmd} of {parent_name} | > ")
                print(f"        +"+('-'*llt)+"+")
            print(" For multiple values, use ',' as delimiter. \n Put nothing if you want to accept the value in bracket. [ ]:",end='\n')
            templ=sys.stdin.readline()
            templ=chomp(templ);
            if templ==None: continue
            __cached_dict__=target_hash
            arr1=re.split(",",templ)
            for ark in arr1 :
                set_hash_value(None,ark)
        elif flg=='-' :
            if debug_mode : print("adding branch "+cmd+" to "+varname)
            __cached_dict__=target_hash
            set_hash_value(None,cmd)

        if debug_mode : print(v.keys())
        children=[f for f in v.keys() if not re.match("(flag|cmd|desc)",f)]
        save_target_hash=target_hash
        for child in children :
            if debug_mode: print("Adding "+child+" to "+str(target_hash))
            for arj in arr1:
                #print("arj="+arj+" ,key="+v[child]['cmd'])
                target_hash=save_target_hash[arj]
                __cached_dict__=target_hash
                set_hash_value(None,v[child]['cmd'])
                __cached_dict__=target_hash
                __traverse_staging_hash(v[child],v[child]['cmd'],arj)

    #walk_dict(app_params,title="After load staging hash into parameters")
    #walk_dict(target_hash,"After load staging hash into parameters")

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
def __print_preview() :
    template=gsets['template_selected']
    cwd=gsets['cwd']
    target=gsets['target']
    templ=''

    wid=preview_banner_width;
    head="+" + "-" * (wid-2) + "+"
    print(head)
    print("| " + pad_s([(wid-4),"Reviewing inputs before start...."]) +" |")
    print(head)
    print("| " + pad_s([(wid-4),"Template name is "+template])+" |")
    print("| " + pad_s([(wid-4),"Target directory is "+target]) +" |")
    print("| " + pad_s([(wid-4),"Working directory is "+cwd]) + " |")
    print(head)
    print("| " + pad_s([(wid-4),"All Parameter List :"]) + " |")
    __print_params()
    print("\nProceed (y|n) [ n ] :",end='')
    templ=sys.stdin.readline()
    templ=chomp(templ)
    print("\nYour choice is "+templ+"\n")

    if re.match("^\s*(y|yes)\s*\Z",templ,re.IGNORECASE) :
        print("Proceeding...")
    else:
        print("Exiting...")
        quit()
    __process_template()

    print("Template "+template+" execution is complete.\n")
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
def __process_template() :
    global __cached_dict__   # avoid duplicate copies of dictionary objects
    global gsets
    global gtree
    global sub_depth

    template=gsets['template_selected']
    dirname=gsets['template_dir']
    target=gsets['target']

    print("Template location is [ "+dirname+" ]")
    print("Extracting files from template [ "+template+" ]")

    tl=path.join(dirname,template)
    files = [f for f in os.listdir(tl) if os.path.isfile(os.path.join(tl, f)) and not (re.match("(^[\.]\s*$|^[\.\.]\s*$)",f) or f ==additional_params_file)]

    for ttl in files:
        #print(f"tl={tl}")
        if debug_mode :print("\nCopying file:["+ttl+"] to "+target+"...")
        sub_depth=0
        if re.match("{{{\s*fi_",ttl) :
            __file_iterator(ttl,tl,target)
            continue
        ## repercussion 1.2.1.b:1
        if re.match("___\w+\.ficf",ttl) : #possibly a fi command file
            #print(f"Hi, this could be a fi command file tl={tl} ttl={ttl}!")
            #print(f"Peak first line of the file")
            FH=open(path.join(tl,ttl),"r")
            fst_idx=0
            fst_l=FH.readline().rstrip()
            #print(f"First line is {fst_l}")
            if re.match("^\s*{{{\s*fi_begin\s*}}}\s*$",fst_l) :
                if debug_mode : print("this is fi command file!!!")
                fst_idx+=1
                fi_cmd=""
                while True:
                    fst_l=FH.readline().rstrip()
                    if fst_l==None : break
                    if re.match("^\s*{{{\s*fi_end\s*}}}\s*$",fst_l) :
                        fst_idx+=1
                        break
                    fi_cmd+=fst_l+"\n"
                    fst_idx+=1
                fi_cmd=fi_cmd.rstrip("\n")
                if debug_mode : print(f"fi_cmd is {fi_cmd}, fst_idx={fst_idx}")
                if re.match("{{{\s*fi_",fi_cmd) :
                    FH.close()
                    old_gtree=gtree
                    __init_gtree()
                    print(f"Detected command file, {ttl}, creating file(s) based on its directives...")
                    __file_iterator(ttl,tl,target,fi_cmd,fst_idx) # calling new revision of this function
                    print(f"Done with {ttl}.")
                    gtree=old_gtree
                    continue
            FH.close()

        ntl=__substitute_string(ttl)
        if (debug_mode and sub_depth<0) : print("<<< File "+ttl+" was processed by top level function.")
        if (sub_depth==-1) : print("Complete.")
        if (sub_depth==-1 or sub_depth==-2) : continue

        sub_depth=1    # checking file content

        FS = open(path.join(tl,ttl), "r")
        lines= FS.readlines()
        FS.close()


        print("Processing file content")

        nlines=None
        #print "before processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
        __init_gtree()          # pass no arguments
        gtree['source']=lines   # instead, assign directly, avoid pass args by value to save memory
        gtree['total_lines']=len(lines)
        __process_file_content()
        nlines=gtree['nlines']  # must get it back, otherwise it might be a different one
        #print "after processing $gtree->{nlines}, " . scalar @nlines . "\n" if ($debug_mode2);
        print("Creating "+path.join(target,ntl))

        FH=open(path.join(target,ntl),"w")
        # changed from tl to tll 1.2.1
        for tll in nlines:
            FH.write(tll+"\n")
        FH.close()
        print("Complete.")
    pass
########################################################################################
# substitute_string
#  proc_id : 0080
# argument : string contains substitution variable or plain text
#  purpose : replace all substitution variables with their provided values in whereever the appear in the tempalte file
#  pre     : parse_template & process_template are called
#  post    : call __run_tester which is the actual worker routine
########################################################################################
def __substitute_string(tl) :
    final=__run_tester(tl)
    #print "final string is $final\n";
    return final
########################################################################################
# run_tester
#  proc_id : 0081
# argument : string contains substitution variable or plain text
#  purpose : this is associated worker routine assisting substitute_string
#  pre     : parse_template & process_template are called
#  post    :
########################################################################################
def __run_tester(tl) :
    if debug_mode and verbose_mode : print("processing input line is "+tl)
    if assign_expr(None,re.search("(.*){{{(((?!}}}).)*)}}}(.*)",tl)) :
        m=get_last_assign()
        prev=m.group(1)
        proc=m.group(2)
        post=m.group(4)
        f,p,t='','',''

        if debug_mode and verbose_mode : print("S1=%s, S2=%s, S4=%s",prev,proc,post)

        if assign_expr(None,re.match("^\s*(\S+)(\s+|<<<|\{\{\{|\#\#\#)(.+)\s*\Z",proc)) :
            m=get_last_assign()
            f,t,p=m.group(1),m.group(2),m.group(3)
            if debug_mode : print("1 f=%s, t=%s, p=%s"%(f,t,p))
            if t=='<<<'   : p="<<<"+p
            if t=='{{{'   : p="{{{"+p
            if debug_mode : print(f"function name is {f}")
            p=__run_tester(p)
            if debug_mode : print(f"parameter is {p}")
            #print "$p is a ARRAY ref, passing to __run_func $f\n" if ($debug_mode && ref $p);
            proc=__run_func(f,p,proc)
        elif assign_expr(None,re.match("^\s*(\S+)\s*\Z",proc)) :
            m=get_last_assign()
            f=m.group(1);
            if debug_mode : print("f=%s, t=%s, p=%s",f,t,p)
            if debug_mode : print(f"function name is {f}")
            proc=__run_func(f,p,proc)

        # more operations might be required here <<<<<<<
        if isinstance(proc,dict) or isinstance(proc,list) :
            if debug_mode and verbose_mode : print("return value is a ref, stack it : "+str(proc))
            proc=__stack_func_ref(proc)
            proc=" ###"+proc+"### "
        return __run_tester(concat([prev,proc,post]) )
    elif assign_expr(None,re.match("(.*)<<<(((?!>>>).)*)>>>(.*)",tl)) :
        m=get_last_assign()
        prev=m.group(1)
        proc=m.group(2)
        post=m.group(4)
        if debug_mode : print("S1=%s, S2=%s, S4=%s",prev,proc,post)
        prev=__run_tester(prev)
        post=__run_tester(post)
        proc=__fetch_variable(proc)

        if (isinstance(proc,dict) or isinstance(proc,list)):
            if debug_mode : print("It is array/hash ref, saving to stack_func_refs")
            proc=__stack_func_ref(proc)
            if debug_mode : print("returned "+proc)
            proc=" ###"+proc+"### "
            #return proc

        arr_refs[proc]=proc
        #print("concatenating %s,%s,%s to "%(prev,proc,post)+concat([prev,proc,post],":"))
        return concat([prev,proc,post])
    elif assign_expr(None,re.match("^([^\"]*)\"([^\"]+)\"(.*)",tl)) :
        m=get_last_assign()
        prev=m.group(1)
        post=m.group(3)
        proc=m.group(2)

        #print "found enclosed string S1=$prev, S2=\"$proc\", S3=$post\n" if ($debug_mode);
        prev=__run_tester(prev)
        post=__run_tester(post)
        #print "Returning string $prev\"$proc\"$post\n" if ($debug_mode);

        return prev+"\""+proc+"\""+post
    else :
        return tl
########################################################################################
# file_iterator
#  proc_id : 0090 (1.2.1.b.1.1)
# argument : filename_command, source_dir, target_dir
#  purpose : filter iterator is a utility to generate multiple files based on the fi commands
#  pre     : parse_template & get_variable_values are called.
#  post    : based on the criteria provided in the filename_command, multiple files are to be created
# update  :
#          repercussion 1.2.1.b.1.1 : adding more parameters to handle fi command file
#               fi_cmd : the command for gi_gen
#               start_pos : where the real content begins
########################################################################################
def __file_iterator(filename,sdir,tdir,fi_cmd=None,start_pos=0) :
    global __cached_dict__
    global gtree

    if debug_mode : print(f'file_iterator is called, filename={filename}, source={sdir}, target={tdir}')
    #you need to find the exact match of the function and its paramater
    m=None
    fi_type=1
    fi_command=filename
    fi_filename=filename
    fi_startpos=0
    if fi_cmd !=None :
        fi_type=2
        fi_command=fi_cmd
        fi_startpos=start_pos

    if assign_expr(None,re.match("(((?!{{{fi_).)*)\{\{\{\s*fi_(\w+)(\s+)(.+)$",fi_command)) :
        m=get_last_assign()
        #found file iterator function
        fn= m.group(3)
        h = m.group(1)
        t = m.group(5)
        #pgroups(m,10,1,0,"Matching file iterator")
        #if debug_mode : print(f"file_iterator : m.groups: {m.group()} , m.span: {m.span()}")
        #################
        #gen2 sub routine
        if fn =='gen2' :
            pos=__find_match('{{{','}}}',t) # find body of fi_gen2 function
            #print(f"pos={pos}");
            body = substr(t,0,pos)
            if debug_mode : print(">>>>>  find pos=%s body=%s"%(pos,body))

            if assign_expr(None,re.match("\s*(\w+)\s+in\s+(.+)$",body)) :
                m=get_last_assign()
                var1=m.group(1)
                r=m.group(2)
                #if debug_mode : print("var1=%s, r=%s" % (var1,r))
                posd=__find_first_collection(r)
                if debug_mode : print(f">>>>> First Collection Detection : posd={posd!r}")
                body2=posd[3]
                var2=None
                if assign_expr(None,re.match("\s*(\w+)\s+in\s+(.+)",body2)) :
                    m=get_last_assign()
                    var2=m.group(1)
                    r=m.group(2)
                else:
                    print(f"Syntax Error while parsing gi_gen2 function : {body2}")
                    return

                #print(f"var2={var2}, r={r}")

                typ=posd[1]
                arr1=None
                if typ=='s' :
                    try:
                        col=app_params[posd[2]]
                    except KeyError:
                        col=None
                    #print(f"col={col!r}")
                    if isinstance(col,dict) :
                        arr1=list(col.keys())
                    if debug_mode : print(f"arr1={arr1!r}, var1={var1}, typ={typ}")

                posd2=__find_first_collection(r)
                if debug_mode : print(f">>>>> First Collection Detection : posd2={posd2!r}")

                if re.match("^\s*hash_keys",posd2[2]) :
                    oldv = get_hash_value(gtree,'stack',var1)
                    gi_param=posd2[3]
                    if debug_mode : print(f"oldv={oldv!r}, gi_param={gi_param}")
                    for tii in arr1:
                        __cached_dict__=gtree
                        set_hash_value(None,'stack',var1,tii)
                        hd=__run_func('hash_keys',substr(posd2[2],posd2[0]+9),posd2[2])
                        if debug_mode : print(f"-->hd={hd!r}")
                        result=[] if hd==None else list(hd.keys())
                        if debug_mode : print(f"result is {result!r}")
                        oldvj=get_hash_value(gtree,'stack',var2)
                        for tjj in result :
                            __cached_dict__=gtree
                            set_hash_value(None,'stack',var2,tjj)
                            argline=__translate_stacked_vars(gi_param)
                            if debug_mode : print(f"going to gen files with {argline}")
                            gi_fname=None
                            gi_args=None
                            # bug: 1.2.1.b.
                            if assign_expr(None,re.search("fi_name\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)",argline)):
                                m=get_last_assign()
                                if debug_mode : pgroups(m,10,1,1,"fi_name")
                                gi_fname=m.group(1)
                                gi_args=m.group(5)
                                gi_fname=gi_fname.strip()
                                if gi_args =='fi_args' :
                                    if assign_expr(None,re.search("fi_args\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)",argline)):
                                        m=get_last_assign()
                                        if debug_mode : pgroups(m,7,1,1,"fi_args")
                                        gi_args=m.group(1)
                                if debug_mode: print("Going to create file "+path.join(tdir,gi_fname)+f" with args {gi_args}")
                                gi_target=path.join(tdir,gi_fname)
                                if debug_mode : print(f"source={fi_filename},target={gi_target}")
                                if fi_startpos<=0:
                                    __run_func('fi_writefile',f"source={fi_filename};target={gi_target};args={gi_args}")
                                else:
                                    # repercussion : 1.2.1.b.5
                                    __run_func('fi_writefile',f"source={fi_filename};target={gi_target};args={gi_args};startpos={fi_startpos}")
                            else:
                                print(f"Failed to get filename from {argline}")
                        if oldvj!=None:
                            gtree['stack'].update({var2,oldvj})
                        else:
                            gtree['stack'].pop(var2,None)
                    if oldv!=None:
                        gtree['stack'].update({var1:oldv})
                    else:
                        gtree['stack'].pop(var1,None)
            else:
                print(f"Syntax wrong:{body}"+"\n  should be \"{{{fi_gen2 var in collection1 collection2 }}}\"")
        ###################
        # gen1 sub routine
        elif fn == 'gen1': #interation of a hash/array
            pos=__find_match('{{{','}}}',t) # find body of fi_gen2 function
            body = substr(t,0,pos)
            if debug_mode : print(f">>>>>  find pos={pos} body={body}")
            if assign_expr(None,re.match("^\s*(\w+)\s+in\s+(.+)$",body)):
                m=get_last_assign()
                var1=m.group(1)
                set=m.group(2)
                arglist_orig=''

                posd2=__find_first_collection(set)
                if debug_mode:
                    print(f">>>>> First Collection Detection : posd2={posd2}")

                if posd2[1] == 'h':
                    pass
                elif posd2[1] == 's' :
                    set=f"<<<{posd2[2]}>>>"
                    arglist_orig=posd2[3]
                if debug_mode and verbose_mode :
                    print(f"var1={var1}, set={set}, arglist_orig={arglist_orig}")
                set=__translate_stacked_vars(set);
                set= __substitute_string(set)
                set=__fetch_stacked_vars(set);
                if debug_mode : print(f"set={set}")
                oldvj=gtree['stack'].get(var1)
                result=None
                if isinstance(set,dictionary):
                    result=set.keys()
                elif isinstance(set,list):
                    result=set
                else:
                    result=[set]

                for tjj in result:
                    __cached_dict__=gtree
                    set_hash_value(None,'stack',var1,tjj)
                    argline=arglist_orig
                    argline=__translate_stacked_vars(argline);
                    argline=__substitute_string(argline);
                    if debug_mode and verbose_mode:
                        print(f"going to gen files with {argline}")
                    gi_fname=None
                    gi_args=None
                    if assign_expr(None,re.search("fi_name\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)",argline)) :
                        m=get_last_assign()
                        if debug_mode and verbose_mode:
                            pgroups(m,10,1,1,'fi_name')

                        gi_fname=m.group(1)
                        gi_args=m.group(5)
                        gi_fname=gi_fname.rstrip()
                        gi_target=path.join(tdir,gi_fname)
                        if gi_args == 'fi_args' :
                            if assign_expr(None,re.search("fi_args\s*:\s*((((?!(fi_name|fi_args)).))*)\s*(fi_name|fi_args|$)",argline) ) :
                                m=get_last_assign()
                                if debug_mode and verbose_mode :
                                    pgroups(m,10,1,1,'fi_args')
                                gi_args=m.group(1)
                        #print "Going to create file $tdir/$gi_fname with args $gi_args \n";
                        if fi_startpos<=0:
                            __run_func('fi_writefile',f"source={fi_filename};target={gi_target};args={gi_args}")
                        else:
                            # repercussion : 1.2.1.b.5
                            __run_func('fi_writefile',f"source={fi_filename};target={gi_target};args={gi_args};startpos={fi_startpos}")
                    else:
                        print(f"Failed to get filename from {argline}")

                if oldvj!=None:
                    gtree['stack'].update({var1:oldvj})
                else:
                    gtree['stack'].pop(var1)
        ###################
        # genx sub routine, can handle endless nested hash/arrays , will replace gen1 and gen2 later
        # }elsif ($fn eq 'genx'){ #interation of a hash/array
        #     my $ph={};
        #     $ph->{str}=$filename;
        #     $ph->{type}='r';
        #     $ph->{nodeidx}=0;
        #     $ph->{status}='idle';
        #     my @arr=__find_nested_pairs('{{{','}}}',$ph);
        #     walk_dict($ph,1,1,"Test Only");
        # }

########################################################################################
# implement_fo
#  proc_id : 0091
#  purpose : called by implement_fo as worker subroutine to set file permission
########################################################################################
def implement_fo(vt,fh):
    if vt!=None and fh !=None :
        oh=vt.get('file_options')
        if oh==None: return
        for k in (oh.keys()) :
            if (k == 'chmod') :
                v=oh['chmod']
                if v!=None and re.match("^\s*\d+\s*$",v) :
                    if debug_mode : print(f"..changing file permission for {fh} to {v}")
                    os.chmod(fh,int(v,8))
########################################################################################
# implement_fo
#  proc_id : 0092
#  purpose : called by implement_fo as worker subroutine to set file permission
########################################################################################
def clear_fo(vt) :
    if vt!=None : vt['file_options']=None
########################################################################################
# process_file_content
#  proc_id : 0100
# argument : none
#  purpose : process file content before write to target directory
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited
#  post    :
########################################################################################
def __process_file_content(lines=None) :
    __explore_file()
    if debug_mode2 and verbose_mode :
        print(" gtree content after processing....")
        __print_gtree()
    __translate_tree(None)
########################################################################################
# explore_file & explore_file_line & get_current_line
#  proc_id : 0110
# argument : none
#  purpose : process file content before write to target directory
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited
#  post    :
########################################################################################
def __explore_file() :
    global gtree
    #if debug_mode and verbose_mode:
        #print(" gtree content before exploring....")
        #__print_gtree()
    line=__get_current_line()
    line=chomp(line)
    if debug_mode2 : print("current line is "+line)

    __explore_file_line(line)
    ___prev_tl=line

    if debug_mode : print("current_line=%d,total_lines=%d"%(gtree['current_line'],gtree['total_lines']))

    if  gtree['current_line'] >= gtree['total_lines'] :
        return
    else :
        return __explore_file()
########################################################################################
# get_current_line
#  proc_id : 0111
# argument : none
#  purpose : iterate lines one for each call
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited
#  post    :
########################################################################################
def __get_current_line() :
    global gtree
    idx=gtree['current_line']
    #print("idx="+str(idx))
    gtree['current_line']=idx+1
    ## repercussion 1.2.1.b:2
    try:
        return gtree['source'][idx]
    except IndexError :
        return ""
########################################################################################
# explore_file_line
#  proc_id : 0112
# argument : none
#  purpose : process file content before write to target directory
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited
#  post    :
########################################################################################
def __explore_file_line(tl) :
    global gtree
    global cls_defs
    global sub_defs
    global __cached_dict__
    global ___prev_tl

    # curr_tree=gtree['curr_tree']
    if re.match("^\s*{{{\s*skip(.)*$",tl): return
    tnid=gtree['curr_tnid']
    #print("-------------------------------- gtree.curr_tnid is "+tnid);
    curr_tree=__get_tree_by_tnid(tnid)
    #print("---------------------------------curr_tree.tnid is "+curr_tree['tnid'])

    #if debug_mode2 and verbose_mode : walk_dict(curr_tree,title="curr_tree content curr_tnid="+tnid)

    if curr_tree==None or curr_tree==gtree :
        if debug_mode2 :
            print("gtree->{curr_tree} is root now ")
        curr_tree=gtree
    else :
        if debug_mode2 :
           print("gtree->{curr_tree} is defined, now is a subtree");

    nid=curr_tree['current_node']
    if (debug_mode2) : print("Exploring line [nid="+str(nid)+"] : "+tl   )
    tree_node_type=curr_tree.get('type')
    tree_node_var=curr_tree.get('var')

    m=None
    if tree_node_type == 'clsdef' : # classdef lines will be parsed separately when all lines are loaded
        if re.match("^\s*class\s*}}}\s*$",tl):
            if debug_mode3 :
                print(f"Detected end of class definition.\nStart parsing it and if succeed, will go back to parent node.")
            __cached_dict__=curr_tree
            set_hash_value(None,'status','pending-close')

            if debug_mode:
                print(f"Adding reference {tree_node_type} of {tree_node_var} to cls_defs")

            __cached_dict__=cls_defs
            set_hash_value(None,tree_node_var,'r',curr_tree)

            old_gtree=gtree
            olaa=curr_tree.get('raw_lines')
            old_subdefs=sub_defs
            __cached_dict__=cls_defs
            set_hash_value(None,tree_node_var,'methods',{})
            sub_defs=get_hash_value(None,tree_node_var,'methods')
            __init_gtree(olaa)
            if debug_mode :
                __cached_dict__=gtree
                walk_dict(None,1,1,"Before process cls_def")
            for tline in (olaa):
                __explore_file_line(tline)
                ___prev_tl=tline

            __cached_dict__=curr_tree
            curr_tree['status']='close';
            __cached_dict__=cls_defs
            set_hash_value(None,tree_node_var,'r',gtree)
            __translate_tree(gtree)
            gtree['superclass']=curr_tree.get['superclass']
            gtree['type2']='clsdef'
            gtree['curr_tree']=None
            if debug_mode:
                walk_dict(cls_defs,1,1,"After process cls_def")
            gtree=old_gtree
            sub_defs=old_subdefs;
            gtree['curr_tnid']=curr_tree['parent_tnid']
            return
        if debug_mode3: print(f"adding plain line into class definition {curr_tree}")
        arr=curr_tree.get('raw_lines')
        if arr!=None:  arr.append(tl)
        return
    elif tree_node_type == 'subctrl' :  # sub lines will only be translated each time it is called
        tree_node_var=None
        try :
            tree_node_var=curr_tree.get('var')
        except KeyError :
            tree_node_var=None
        if re.match("^\s*sub\s*}}}\s*$",tl) :
            if debug_mode3 : print("Detected end of sub definition.\nGo back to parent node.")
            curr_tree['status']='close'
            print("Adding reference "+tree_node_type+" of "+tree_node_var+" to sub_defs")
            __cached_dict__=sub_defs
            set_hash_value(None,tree_node_var,'r',curr_tree)
            gtree['curr_tnid']=curr_tree['parent_tnid']
            #### to be removed: gtree['curr_tree']=curr_tree['parent']
            return
        if debug_mode3 : print("adding plain line into subroutine definition " + str(curr_tree))
        arr=[]
        try :
            arr=curr_tree['raw_line']
        except KeyError:
            curr_tree['raw_line']=arr
        arr.append(tl)
        return;
    elif re.match("{{{\s*foreach(\s+|\Z)",tl) :
        if assign_expr(m,re.match("^\s*{{{\s*foreach\s+(\w+)\s+(in)\s+(.+)\Z",tl)) :
            m=get_last_assign()
            if debug_mode2 : print("**** Found foreach structure variable=%s,list=%s",m.group(1),m.group(3))
            nid+=1
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'t','f')
            sub_node={}
            sub_tnid=tnid+"-"+str(nid)
            __cached_dict__=sub_node
            sub_node['tnid']=sub_tnid;
            sub_node['stack']={}
            set_hash_value(None,'type','foreach')
            set_hash_value(None,'current_node',0)
            set_hash_value(None,'level',curr_tree['level']+1)
            set_hash_value(None,'parent_tnid',tnid)
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'r',sub_node)
            set_hash_value(None,'current_node',nid)
            __cached_dict__=sub_node
            set_hash_value(None,'list',m.group(3))
            set_hash_value(None,'var',m.group(1))
            set_hash_value(None,'status','open')
            __cached_dict__=gtree
            set_hash_value(None,'curr_tree',sub_node)
            set_hash_value(None,'curr_tnid',sub_tnid)
            if debug_mode2: print("continue with sub tree of foreach.")
        else :
            print("Invalid foreach statement!! Corrent and try again.\n **** "+tl)
            pass
    elif re.match("^\s*foreach\s*}}}\s*\Z",tl) :
        if debug_mode2 : print("**** Found end of foreach structure")
        if curr_tree==None or curr_tree['type']!='foreach' :
            print("**** Error! Found foreach}}}, but it is not in a foreach loop.\n code=%s"%(tl))
        else:
            ### go back to parent
            curr_tree['status']='close'
            __cached_dict__=gtree
            ptnid=curr_tree['parent_tnid']
            gtree['curr_tnid']=ptnid
            #set_hash_value(None,'curr_tnid',ptnid)
            ptree=__get_tree_by_tnid(ptnid)
            #if ptree==gtree: gtree['curr_tree']=None
            #else: gtree['currr_tree']=ptree
            if debug_mode2 : print("go back to parent node")
    elif re.match("{{{\s*case(\s+|\Z)",tl) :
        if debug_mode3 : print("**** Found case structure and checking its sub-type")
        if re.match("^\s*{{{\s*case(\s*)\Z",tl) :
            if debug_mode3 : print("**** Found sub-type is case-condition")
            nid+=1
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'t','cd') # type is case-condition
            sub_node={}
            sub_tnid=tnid+"-"+str(nid)
            sub_node['tnid']=sub_tnid
            sub_node['stack']={}
            sub_node['type']='ccctrl' # sub tree is case-condition
            sub_node['current_node']=0
            sub_node['level']=curr_tree['level']+1
            sub_node['parent_tnid']=curr_tree['tnid']
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'r',sub_node)
            curr_tree['current_node']=nid
            sub_node['vartype']='d'
            sub_node['status']='open'
            #gtree['curr_tree']=sub_node
            gtree['curr_tnid']=sub_tnid
            if debug_mode2: print("continue with sub tree of case-condition.")
        elif assign_expr(m,re.match("^\s*{{{\s*case\s+(\S+)(.*)\Z",tl)): # it's possibly a case_switch structure
            m=get_last_assign()
            tl=m.group(1)+m.group(2) # check content
            tvar=None
            vtype=None

            if assign_expr(m,re.match("^\s*###\s*(\S+)\s*###\s*\Z",tl)) : # use dynamic stack variable as switch
                m=get_last_assign()
                if debug_mode3 : print("**** Found sub-type is case-switch, and the switch is dynamic stack variable "+m.group(1))
                tvar=m.group(1)
                vtype='d' # dynamic;
                tvar=tvar.strip()
                tvar="###"+tvar+"###"
            elif assign_expr(m,r.match("^(.*){{{(((?!}}}).)*)}}}(.*)\Z",tl)) : # use dynamic function & variable as switch
                m=get_last_assign()
                if debug_mode3 : print("**** Found sub-type is case-switch, and the switch is dynamic stack variable "+m.group(1))
                tvar=m.group(2)
                vtype='d' # dynamic;
                tvar=tvar.strip()
                tvar="{{{"+tvar+"}}}"
            elif assign_expr(m,re.match("^\s*<<<\s*(\S+)\s*>>>\s*\Z",tl)) : # use fixed global variable as switch
                m=get_last_assign()
                if debug_mode3 : print("**** Found sub-type is case-switch, and the switch is fixed substitution variable "+m.group(1))
                tvar=__fetch_variable(m.group(1))
                tvar=tvar.strip()
            else:
                print("**** Error ! case-switch structure can only use <<<substitution variable>>> as switch-variable,\n To use stack variable or other dynamic conditions such as function and expression, you have to use case-condition structure.")
            nid+=1
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'t','cs') # caseswitch
            sub_node={}
            sub_tnid=tnid+"-"+str(nid)
            sub_node['tnid']=sub_tnid
            sub_node['stack']={}
            sub_node['type']='csctrl' # sub tree is case-switch
            sub_node['current_node']=0
            sub_node['level']=curr_tree['level']+1
            sub_node['parent_tnid']=curr_tree['tnid']
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'r',sub_node)
            set_hash_value(None,'current_node',nid)
            sub_node['var']=tvar
            sub_node['vartype']=vtype
            sub_node['status']='open'
            gtree['curr_tree']=sub_node
            gtree['curr_tnid']=sub_tnid
            if debug_mode2 :print("continue with sub tree of case-switch-variable, switch is "+tvar)
        else:
            print("Invalid foreach statement!! Corrent and try again.\n **** "+tl)
    elif (re.match("{{{\s*else\s+then\s*\Z",tl)) :
        if debug_mode3 : print("tl is %s , match anyway."%(tl))
        ctype=curr_tree['type']
        vtype=curr_tree.get('vartype')
        if debug_mode3 : print("**** Detected else-branch of case structure")
        if (curr_tree==None or (ctype!='csctrl' and ctype!='ccctrl')) :
            print("Error! Found {{{else, but it is not in a case structure.\n code="+tl)
            quit()
        elif curr_tree['status'] == 'close-skip' :
            if debug_mode3 : print("case structure already matched, now it is looking for case}}}")
            curr_tree['when_but_skip']=1
        else:
            if vtype=='d' :
                if debug_mode3 or debug_mode3 : print(">>>>> adding dynamic else-branch node.")
            else:
                if debug_mode3 or debug_mode2 : print(">>>>> condition matches switch, adding branch node.")
            nid=curr_tree['current_node']
            nid+=1
            sub_node={}
            sub_tnid=tnid+"-"+str(nid)
            sub_node['tnid']=sub_tnid
            sub_node['stack']={}
            sub_node['type']='when-branch'  # sub tree
            sub_node['stype']='else'        # sub tree
            sub_node['current_node']=0
            sub_node['level']=curr_tree['level']+1
            #sub_node['parent}=$curr_tree->{parent}; # go to grand-parent as case-when is a 2-layer structure
            sub_node['parent_tnid']=tnid
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'r',sub_node)
            curr_tree['current_node']=nid
            curr_tree['tnid']=tnid
            sub_node['var']=None
            sub_node['status']='open'
            curr_tree['status']='in-child'
            if debug_mode3:
                print("adding child to %s : nid=%d : status=%s, child is %s"%(curr_tree['type'],nid,curr_tree['status'],sub_node['type']))
            gtree['curr_tnid']=sub_tnid
    elif assign_expr(None,re.match("{{{\s*when\s+(.+)\s+then\s*\Z",tl)) :
        m=get_last_assign()
        cont=m.group(1)
        cont=cont.strip()
        vtype=curr_tree.get('vartype')

        if debug_mode3 : print("tl is %s, cont is %s, vtype=%s"%(tl,cont,vtype))
        ctype=curr_tree['type']

        if debug_mode3 : print("**** Detected when-branch of case structure")
        if (curr_tree==None or (ctype!='csctrl' and ctype !='ccctrl')):
            print("**** Error! Found {{{when, but it is not in a case structure.\n code="+tl)
            quit()
        elif curr_tree['status']=='close-skip' :
            if debug_mode3 : print("case structure already matched, now it is looking for case}}}")
            curr_tree['when_but_skip']=1
        else:
            if debug_mode3 :
                print("... ... parse and add child node to %s (var=%s)"%(ctype,curr_tree.get('var')))
            if ctype =='csctrl' or ctype=='ccctrl' :
                if debug_mode3:
                    print("checking %s, switch is %s, condition is %s"%(ctype,curr_tree.get('var'),cont))
                if curr_tree.get('var') != cont and vtype!='d' :  # if dynamic, will collect all branches
                    curr_tree['status']="skip"
                    if debug_mode3 :
                        print(">>>>> condition does not match switch, skipped. %s %s"%(curr_tree['status'],curr_tree['type']))
                    return
                if vtype == 'd' :
                    if debug_mode3: print(">>>>> adding dynamic branch node.")
                else:
                    if debug_mode3: print(">>>>> condition matches switch, adding branch node.")

                nid=curr_tree['current_node']
                nid+=1
                sub_node={}
                sub_tnid=tnid+"-"+str(nid)
                sub_node['tnid']=sub_tnid
                sub_node['stack']={}
                sub_node['type']='when-branch' # sub tree
                sub_node['current_node']=0;
                if vtype=='d' : sub_node['cont']=cont
                sub_node['level']=curr_tree['level']+1
                #sub_node['parent']=$curr_tree->{parent}; # go to grand-parent as case-when is a 2-layer structure
                sub_node['parent_tnid']=curr_tree['tnid']
                __cached_dict__=curr_tree
                set_hash_value(None,'nodes',nid,'r',sub_node)
                curr_tree['current_node']=nid
                sub_node['var']=curr_tree.get('var')
                sub_node['status']='open';
                sub_node['vartype']=curr_tree.get('vartype')
                curr_tree['status']='in-child'
                if debug_mode3 :
                    print("adding child to %s : nid=%d : status=%s, child is %s"%(curr_tree['type'],nid,curr_tree['status'],sub_node['type']))
                gtree['curr_tnid']=sub_tnid
    elif (re.match("^\s*when\s*}}}\s*\Z",tl)) :
        if debug_mode2: print("**** Found end of when structure")
        vtype=curr_tree.get('vartype')
        if (curr_tree==None or curr_tree['type']!='when-branch'):
            if curr_tree['status']=='skip' and (curr_tree['type']=='csctrl' or curr_tree['type']=='ccctrl') :
                if debug_mode3 : print("End of skipped block, scanning for next branch.")
                curr_tree['status']='open'
                return
            else:
                if debug_mode3 : print("special place , status=%s, type=%s"%(curr_tree['status'],curr_tree['type']))

            if curr_tree['when_but_skip']==1 :
                if debug_mode3 : print("current block is being skipping, closed. "+tl)
                curr_tree['when_but_skip']=0
            else:
                print("**** Error! Found when}}}, but it is not in a when-branch of case structure.\n code="+tl)
        else:
            ### go back to parent
            if curr_tree['type'] == "when-branch" :
                curr_tree['status']='close'
                gtree['curr_tnid']=curr_tree['parent_tnid']
                ntree=__get_tree_by_tnid(gtree['curr_tnid'])
                if ntree['type']=='csctrl' or ntree['type']=='ccctrl' :
                    if vtype!='d' : ntree['status']='close-skip'
                if debug_mode2 : print("go back to parent node and close")
    elif re.match("^\s*case\s*}}}\s*\Z",tl) :
        if debug_mode2:
            print("**** Found end of case structure, current type=%s, status = %s"%(curr_tree['type'],curr_tree['status']))
        if curr_tree!=None and (curr_tree['type']=='csctrl' or curr_tree['type']=='ccctrl'):
            if re.match("close-skip|open|in-child",curr_tree['status']) :
                if debug_mode2 : print(">>> Successful end of case structure. Go back to parent node.")
            elif curr_tree['status']=='skip' :
                print("**** Error! Found case}}} while when-then statement is not closed. Force close current case structure. line: "+tl)
            else:
                print("**** Error! Wrong status of case strucure. Force close current case structure. line: "+tl)
            curr_tree['status']='close'
            gtree['curr_tnid']=curr_tree['parent_tnid']
        else:
            print("**** Error!! Found invalid case}}}.")
            return
    elif re.match("{{{\s*while\s+",tl) :
        if assign_expr(m,re.match("^\s*{{{\s*while\s+\((.+)\)\Z",tl)) :
            m=get_last_assign()
            print("m="+str(m))
            if debug_mode2 : print("**** Found while structure condition="+m.group(1))
            nid+=1
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'t','l') # while-loop
            sub_node={}
            sub_tnid=tnid+"-"+str(nid)
            sub_node['tnid']=sub_tnid
            sub_node['stack']={}
            sub_node['type']='while'; # sub tree
            sub_node['current_node']=0
            sub_node['level']=curr_tree['level']+1
            sub_node['parent_tnid']=curr_tree['tnid']
            __cached_dict__=curr_tree
            set_hash_value(None,'nodes',nid,'r',sub_node)
            curr_tree['current_node']=nid
            sub_node['cont']=m.group(1)
            sub_node['status']='open'
            gtree['curr_tnid']=sub_tnid
            if debug_mode2 : print("continue with sub tree of while.")
        else:
            print("Invalid While statement!! Corrent and try again.\n **** "+tl+"\n correct syntax : \n {{{while (condition)\n ...\n while}}}")
    elif re.match("^\s*while\s*}}}\s*\Z",tl) :
        if debug_mode2 : print("**** Found end of while structure.")
        if curr_tree==None or curr_tree['type']!='while' :
            print("Error! Found while}}}, but it is not in a while loop.\n code="+tl)
        else:
            ### go back to parent
            curr_tree['status']='close'
            gtree['curr_tnid']=curr_tree['parent_tnid']
            if debug_mode2: print("go back to parent node.")
    elif assign_expr(None,re.match("{{{\s*sub\s+(\w+)\((.*)\)\s*$",tl)) :
        m=get_last_assign()
        subname=m.group(1)
        arglist=m.group(2)

        if debug_mode : print("**** Found subroutine definition "+subname+", start parsing...")
        arglist=arglist.strip()
        arg_arr=re.split(",",arglist)
        arg_arr= [item.strip() for item in arg_arr];
        if debug_mode3 : print("arglist is "+arg_arr)

        nid+=1
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'t','subdef') # caseswitch
        sub_node={}
        sub_tnid=tnid+"-"+str(nid)
        sub_node['tnid']=sub_tnid
        sub_node['stack']={}
        sub_node['type']='subctrl'  # sub tree is case-switch
        sub_node['var']=subname;
        sub_node['current_node']=0
        sub_node['level']=curr_tree['level']+1
        sub_node['parent_tnid']=tnid
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'r',sub_node)
        curr_tree['current_node']=nid
        sub_node['arglist']=arg_arr
        sub_node['raw_lines']=[]
        sub_node['status']='open'
        gtree['curr_tree']=sub_node
        gtree['curr_tnid']=sub_tnid
        #$gtree->{curr_tree}=$sub_node;
        if debug_mode2 : print("continue with subroutine definition : "+subname)
    elif assign_expr(None,re.search("{{{\s*class\s+(\w+)\s*(.*)\s*$",tl)) :
        m=get_last_assign()
        classname=m.group(1)
        arglist=m.group(2)
        superclass=None
        if debug_mode:
            print(f"**** Found class definition {classname}, start parsing...")
        arglist=arglist.strip()
        m=re.search("\s*\:\s*(\w+)\s*$",arglist)
        if m:
            superclass=m.group(1)
        nid+=1
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'t','classdef') # caseswitch
        sub_node={}
        sub_tnid=tnid+"-"+str(nid)
        sub_node['tnid']=sub_tnid
        sub_node['stack']={}
        sub_node['type']='clsdef'  # sub tree is case-switch
        sub_node['var']=classname;
        sub_node['current_node']=0
        sub_node['level']=curr_tree['level']+1
        sub_node['parent_tnid']=tnid
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'r',sub_node)
        curr_tree['current_node']=nid
        sub_node['superclass']=superclass
        sub_node['raw_lines']=[]
        sub_node['status']='open'
        gtree['curr_tnid']=sub_tnid
        gtree['curr_tree']=sub_node
        if debug_mode2:
            print(f"continue with class definition : {classname}.")
    else:
        mtype=curr_tree['type']
        if debug_mode3: print("plain line is being analyzed type=%s, status=%s"%(mtype,curr_tree['status']))
        if re.match("csctrl|ccctrl",mtype) :
            if curr_tree['status'] == 'skip' :
                if debug_mode3 : print("skipping unmatched block line : "+tl)
            elif curr_tree['status'] == 'close-skip' :
                if debug_mode3 : print("case result is already matched, skipping the rest.")
            else:
                print("**** Error : Invalid Line, 'when-then' statement is missing : "+tl)
            return
        nid+=1

        if debug_mode2 : print("plain line, adding to node "+str(nid))
        __cached_dict__=curr_tree
        global __debug_flag
        __debug_flag='a'
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'t','p') # type=plain text
        __cached_dict__=curr_tree
        set_hash_value(None,'nodes',nid,'s',tl) # source
        curr_tree['current_node']=nid
        pass
    pass
########################################################################################
# translate_tree
#  proc_id : 0120
# argument : none
#  purpose : process file content before write to target directory
#  pre     : parse_template & get_variable_values are called. $gtree is properly inited
#  post    :
########################################################################################
def __translate_tree(ctin=None,use_global=0) :
    global __cached_dict__
    global gtree
    global gsets
    fl=None
    ct=None
    if use_global :ct=__cached_dict__
    else: ct=ctin

    if ct==None : ct=__get_tree_by_tnid(gtree['curr_tnid'])

    gtree['curr_tnid']=ct['tnid']

    if debug_mode2 : print("+++++++>>>>> Translating tree "+ct['tnid']+"...")
    if ct != None :
        nodes=ct.get('nodes')
        if (nodes!=None):
            level=ct['level']
            pstr=pad_t([level+2,'-'])
            skipped=0
            for k,v in sorted(nodes.items(),key=lambda x: x[0]):
                if v.get('t') == 'p' :
                    fl=v.get('s')
                    if debug_mode2 : print("old line is "+fl)
                    skipped=is_skipped(fl)
                    if debug_mode2 : print("translating stacked variables....")
                    oldd=__cached_dict__
                    __cached_dict__=ct
                    fl=__translate_stacked_vars(fl,use_global=1)
                    if __cached_dict__!=oldd : __cached_dict__=oldd
                    if debug_mode2 : print("translated line is "+fl)
                    if debug_mode2 : print("substituting global variables....")
                    fl=__substitute_string(fl)
                    if debug_mode2 : print("substituted line is "+fl)
                    if debug_mode2 : print("new line is "+fl)

                    v['n']=fl
                    if debug_mode2 : print_s(["before push to gtree->{nlines}, size is " , len(gtree['nlines'])])
                    if not skipped : gtree['nlines'].append(fl)
                    if debug_mode2 : print_s(["after push gtree->{nlines}, size is ",len(gtree['nlines'])])
                else:
                    sub=v.get('r')
                    if sub != None :
                        oldid=gtree['curr_tnid']
                        gtree['curr_tnid']=sub['tnid']
                        ## dig into sub nodes
                        if debug_mode2 : print("Drill into sub nodes sub:"+sub['tnid'])
                        if debug_mode  : print(" type is %s, var is %s, list is %s"%(sub['type'],sub.get('var'),sub.get('list')))
                        if sub['type'] == 'foreach' :
                            if debug_mode2 : print("Fetching variable %s from %s"%(sub.get('var'),sub.get('list')))
                            va=sub.get('list')
                            vb=None
                            vc=None
                            if va!=None and assign_expr(None,re.match("{{{get_hash_value\s+(\w+)\s+(.+)}}}",va)):
                                m=get_last_assign()
                                vb=m.group(1)
                                vc=m.group(2)
                                if debug_mode2 : print("get_hash_value: hashname is %s, key is %s\n"%(vb,vc))
                                vb=__get_variable_in_scope(vb,sub)
                                if (isinstance(vb,dict) or isinstance(vb,list)) :
                                    if debug_mode2 : print("final hash obj is located : "+vb)
                                    vc=__get_variable_in_scope(vc,sub)
                                    if debug_mode2 : print("final key value is "+vc)
                                    vc=vb.get(vc)
                                    if debug_mode2 : print("final data is "+vc)
                                    svar=sub.get('var')
                                    if (isinstance(vc,list) and svar!=None ):
                                        if debug_mode2 : print("     got keys array")
                                        oldv=sub.get('stack')
                                        if oldv!=None:oldv=oldv.get(svar)
                                        for ix in vc :
                                            if debug_mode2 : print(" Assign %s to %s ... "%(ix,svar))
                                            oldd=__cached_dict__
                                            __cached_dict__=sub
                                            set_hash_value(None,'stack',svar,ix)
                                            __cached_dict__=sub
                                            __translate_tree(None,use_global=1)
                                        if oldv!=None:
                                            __cached_dict__=sub
                                            set_hash_value(None,'stack',svar,oldv)
                                        else:
                                            sub['stack'].pop(svar)
                                    else :
                                        print("****** Error ! Cannot find hash object "+vb+" ******")
                                else:
                                    print("****** Error ! Cannot find hash object "+vb+"  ****** ")
                            elif (assign_expr(None,re.match("{{{hash_keys\s+(\S+)\s*}}}",va))
                              or assign_expr(None,re.match("{{{hash_keys\s+(\S+)\s+(\S+)\s*}}}",va))
                              or assign_expr(None,re.match("{{{hash_keys\s+(\S+)\s+(\S+)\s+(\S+)\s*}}}",va))) :
                                 # function call hash_keys, need to change to call a function named hash_keys

                                #walk_dict(sub,title="+++++++++++++>>>> temp")
                                m=get_last_assign()
                                vb=m.group(1)
                                sk2=m.group(2)
                                sk3=m.group(3)
                                # before parsing, do final substitution
                                vb=__substitute_string(vb)
                                oldd=__cached_dict__
                                __cached_dict__=sub
                                print("vb here is "+str(vb)+" sk2="+sk2+" sk3="+sk3)
                                vc=__fetch_stacked_vars(vb,use_global=1)
                                __cached_dict__=oldd
                                svar=sub.get('var')
                                if (not isinstance(vc,dict) and not isinstance(vc,list)) : # convert it to ref
                                    __cached_dict__=sub
                                    vc=__fetch_stacked_vars(vc,use_global=1)

                                if not isinstance(vc,dict) and not isinstance(vc,list):
                                    print("Invalid list "+vc+" in foreach statement")

                                if debug_mode :
                                    print(">>>>>>> >>>>>>curr_tnid is "+gtree["curr_tnid"])
                                    print("fetching local stacked variable from "+str(vc)+" by key "+str(sk2)+" and its child "+str(sk3))

                                if sk2!=None:
                                    print(">>>>>> >>>>> curr_tnid is "+gtree["curr_tnid"])
                                    sk2=__get_variable_in_scope(sk2,sub)
                                    print(">>>?>> curr_tnid is "+gtree["curr_tnid"])
                                    sk3=__get_variable_in_scope(sk3,sub)
                                    print(">>><><>>> curr_tnid is "+gtree["curr_tnid"])

                                if debug_mode and verbose_mode:
                                    print("sk2=%s, sk3=%s"%(sk2,sk3))

                                if (isinstance(vc,dict) or isinstance(vc,list)):
                                    if sk3!=None :
                                        vc=vc.get(sk2)
                                        if vc!=None: vc=vc.get(sk3)
                                    elif sk2!=None :
                                        vc=vc.get(sk2)

                                print("##############################What is vc=="+str(vc))
                                if (vc!=None and (isinstance(vc,dict) or isinstance(vc,list))):
                                    arr = vc if isinstance(vc,list) else vc.keys()
                                    if debug_mode2 :
                                        print("     got reference")
                                        print("Enter loop")
                                    oldv=__get_value_in_stack(svar)
                                    #my $oldv=__get_value_in_stack($sub->{var},$gtree->{curr_tree});
                                    for tv in arr:
                                        if debug_mode2:
                                            print(" Assign %s to %s ... "%(tv,svar))
                                        __push_stack_vars(svar,tv)
                                        oldd=__cached_dict__
                                        __cached_dict__=sub
                                        __translate_tree(use_global=1)
                                        __cached_dict__=oldd
                                    __restore_value_in_stack(svar,oldv)
                                else:
                                    print("****** Error ! could not found array for "+vb+" ****** ")
                            elif assign_expr(None,re.match("<<<\s*(\w+)\s*>>>",va)) :
                                m=get_last_assign()
                                vb=m.group(1)
                                vc=__fetch_variable(vb)
                                svar=sub.get('var')
                                if debug_mode2 : print("--> "+str(vc))
                                if (isinstance(vc,dict) or isinstance(vc,list)):
                                    if debug_mode2 : print("     got reference")
                                    arr= vc if isinstance(vc,list) else vc.keys()
                                    oldv=sub['stack'].get(svar)
                                    for tv in arr:
                                        if debug_mode2 : print(" Assign %s to %s ... "%(tv,svar))
                                        sub['stack'][svar]=tv
                                        oldd=__cached_dict__
                                        __cached_dict__=sub
                                        __translate_tree(use_global=1)
                                        __cached_dict__=oldd
                                    if oldv!=None :
                                        sub['stack'][svar]=oldv
                                    else:
                                        sub['stack'].pop(svar)
                                else:
                                    print("****** Error ! could not found array for "+vb+" ****** ")
                            elif assign_expr(None,re.match("###\s*(\w+)\s*###",va)) : #if it is defined tree stack variable
                                m=get_last_assign()
                                vb=m.group(1)
                                svar=sub.get('var')

                                vc=__fetch_stacked_vars(vb,sub)

                                print(type(vc))
                                if debug_mode2 :
                                    print_s(["fetching local stacked variable ",vc])

                                if (isinstance(vc,dict) or isinstance(vc,list)) :
                                    if debug_mode2 : print("     got reference")
                                    arr=vc if isinstance(vc,list) else vc.values()
                                    oldv=sub['stack'].get(svar)
                                    for kv in arr:
                                        if debug_mode2 : print(" Assign %s to %s ... "%(kv,svar))
                                        sub['stack'][svar]=kv
                                        oldd=__cached_dict__
                                        __cached_dict__=sub
                                        __translate_tree(None,use_global=1)
                                    if oldv!=None:
                                        sub['stack'][svar]=oldv
                                    else:
                                        sub['stack'].pop(svar)
                                else:
                                    print("****** Error ! could not found array for "+vb+" ***444*** ")
                        elif re.match("csctrl|ccctrl",sub['type']) :
                            if debug_mode3:
                                #print "Exploring case structure sub=$sub, t=$sub->{t}, type=$sub->{type}, status=$sub->{status}, r=$sub->{nodes}->{0}->{r}, nodes=$sub->{nodes} \n" if ($debug_mode3);
                                walk_dict(sub,title="Exploring case structure")
                            nodes=sub['nodes']
                            if debug_mode3 : print_s(["nodes=",nodes])
                            for nk,nv in sorted(nodes.items(),key=lambda x: x[0]):
                                snh=nv.get('r')  # there should be only one child
                                vtype=snh.get('vartype')
                                if debug_mode3:
                                    print("!!!!!!!!!!!!! snh.type=%s,snh.vtype=%s, snh.cont=%s\n"%(snh['type'],vtype,snh.get('cont')))
                                if (vtype=='d'):
                                    # checking conditon
                                    cont=snh.get('cont')
                                    var=snh.get('var')
                                    if var!=None :
                                        oldcr=gtree['curr_tree']
                                        gtree['curr_tree']=snh
                                        oldd=__cached_dict__
                                        __cached_dict__=sub
                                        var=__translate_stacked_vars(var,use_global=1)
                                        __cached_dict__=oldd
                                        var=__substitute_string(var)
                                        if debug_mode3: print("convert var to "+var)
                                        cont=__substitute_string(cont)
                                        if debug_mode3: print("substituted cont is "+cont)
                                        gtree['curr_tree']=oldcr
                                    if sub['type']=='csctrl' :
                                        if var==cont :
                                            oldd=__cached_dict__
                                            __cached_dict__=snh
                                            __translate_tree(use_global=1)
                                            break
                                    elif sub['type']=='ccctrl' :
                                        cont=__translate_stacked_vars(cont,sub)
                                        cont=__substitute_string(cont)
                                        print("evaluate condition "+cont)
                                        cont=reval_expr(cont)
                                        print(["result is ",cont])
                                        if (cont) :
                                            __translate_tree(snh)
                                            break
                                else:
                                    __translate_tree(snh)
                        elif sub['type']=='while' :
                            #print "Exploring while structure sub=$sub, t=$sub->{t}, type=$sub->{type}, status=$sub->{status}, r=$sub->{nodes}->{0}->{r}, nodes=$sub->{nodes} \n" if ($debug_mode3);
                            if debug_mode3:
                                walk_dict(sub,title="Exploring while structure")
                            #nodes=sub['nodes']
                            #if debug_mode3:
                            #    print("nodes="+nodes)
                            cont=sub['cont']
                            if debug_mode3: print("cont is "+cont)
                            cont2=__substitute_string(cont)
                            cont2=__translate_stacked_vars(cont2,sub)
                            if debug_mode3 : print_s(["############################ cont2 is ",cont2," before continue"])
                            j=0
                            global __loop_lmt
                            while (reval_expr(cont2) and j<__loop_lmt) :
                                if debug_mode3 : print_s(["cont state is ",reval_expr(cont2)])
                                oldd=__cached_dict__
                                __cached_dict__=sub
                                __translate_tree(use_global=1)
                                __cached_dict__=oldd
                                cont2=__substitute_string(cont)
                                cont2=__translate_stacked_vars(cont2,sub)
                                j+=1
                        gtree['curr_tnid']=oldid
                    else:
                        if debug_mode2:print("Something is wrong, r is defined in "+sub['r'])
########################################################################################
# is_skipped
#  proc_id : 0130
# argument : none
#  purpose : mark the lines that do not need to appear in the final file
#  pre     : none
#  post    : return 1 for those lines that only take some actions and do not produce lines
########################################################################################
def is_skipped(p):
    if assign_expr(None,re.match("^\s*\{\{\{(\S+)\s*",p)) :
        m=get_last_assign()
        p=m.group(1)
        aa=['define','push_hash','skip','mute','ref','set','sub','get_args','fi_gen2','fo_chmod']
        exists=p in aa
        if exists : return 1
        if re.match("^\s*\#",p) : return 1
    return 0
########################################################################################
# translate_stacked_vars
#  proc_id : 0140
# argument : 1. origin line  2.current tree node
#  purpose : translate the string which has stack variable value (not the global substitution variable)
#  pre     :
#  post    : return 1 for those lines that only take some actions and do not produce lines
########################################################################################
def __translate_stacked_vars(fl,sub1=None,use_global=0):
    global __cached_dict__
    global gtree

    sub=sub1
    if use_global: sub=__cached_dict__
    result=fl
    if sub==None:
        sub=__get_tree_by_tnid(gtree['curr_tnid'])
    if sub==None : sub=gtree

    if debug_mode2 or (debug_mode and verbose_mode) :
        print("sub:translate_stacked_vars:fl=%s,sub=%s\n"%(fl,sub['tnid']))

    if assign_expr(None,re.match("^(((?!###).)*)\#\#\#(\w+)\#\#\#(.*)$",fl)) :
        m=get_last_assign()
        if debug_mode2: print("variable caught")
        if debug_mode : print("match is "+str(m))
        h=m.group(1)
        c=m.group(3)
        t=m.group(4)
        #$h=translate_stacked_vars($h,$sub);
        #$c=sweep_stack($c,$sub);
        c=__fetch_stacked_vars(c,sub)
        if isinstance(c,dict) or isinstance(c,list):
            if debug_mode :
                print("It is array/hash ref, saving to stack_func_refs")
            c=__stack_func_ref(c)
            c=" ###"+c+"### "

        t=__translate_stacked_vars(t,sub)
        fl=h+c+t
        return __translate_stacked_vars(fl) # translate again, in case it has formed new variables dynamically.
    return fl; # give up
########################################################################################
# fetch_stacked_vars
#  proc_id : 0141
# argument : 1. variable name  2.current tree node
#  purpose : get value of provided stack variable name
#  pre     : variable is stacked in the tree node or its ancesters
#  post    :
########################################################################################
def __fetch_stacked_vars(fl,sub1=None,use_global=0) :
    global __cached_dict__
    global gtree

    sub=sub1
    if use_global : sub=__cached_dict__
    final=0
    #print("fl="+str(fl))
    m=re.match("^\s*\###(((?!###).)+)###\s*$",fl)
    if (m) : fl=m.group(1)
    if debug_mode or debug_mode2 :
        print(f"fetching fl=%s, sub={sub!r}")

    if sub==None: sub=__get_tree_by_tnid(gtree['curr_tnid'])
    if sub==gtree or sub==None :
        sub=gtree
        final=1

    #if debug_mode3 and verbose_mode: walk_dict(sub['stack'],title="stack data")

    var=sub['stack'].get(fl)

    if debug_mode or debug_mode2 : print_s(["var is ",var])

    if debug_mode :
        print(f"fetching {fl} with {sub!r} ,{sub.get('super')}")

    if var!=None: return var
    elif sub.get('super')!=None: # && $sub->{r}->{type2} eq 'clsdef'){
        if debug_mode : walk_dict(sub,1,1,'sub in fetch_stacked_vars')
        var=__fetch_stacked_vars(fl,sub['super'].get('r'))
        if var!=None : return var
    if sub==gtree :
        #checking mapping as last resort
        mapped=ref_params.get(fl)
        if debug_mode:
            print("mapped=%s, name=%s "%(mapped,None if mapped==None else mapped.get('name') ))

        if mapped==None or mapped.get('name')==None : return fl
        else:
            return app_params.get(mapped.get('name'))
    else:
        if not final :
            oldd=__cached_dict__
            pid=sub.get('parent_tnid')
            __cached_dict__=__get_tree_by_tnid(pid)
            return __fetch_stacked_vars(fl,use_global=1)
    return fl
########################################################################################
# stack_func_ref
#  proc_id : 0150
# argument : array ref or hash ref
#  purpose : stack array ref or hash ref into subroutine's stack
#  pre     :
#  post    : when extract from stack, use special format for variable name --> ????variable-name????
########################################################################################
def __stack_func_ref(fl,sub1=None,use_global=0):
    global gtree
    sub=sub1
    global __cached_dict__

    if use_global : sub=__cached_dict__
    if sub==None :
       sub=__get_tree_by_tnid(gtree['curr_tnid'])
       if sub==None : sub=gtree
    if debug_mode and verbose_mode:
        print("stacking %s to [tnid=%s]"%(fl,sub['tnid']))

    fx="REF("+gtree['curr_tnid']+"-"+sub['tnid']+"-"+str(random.randint(100,999))+"-"+str(datetime.datetime.now().strftime('%H%M%S'))+")"
    sub['stack'].update({"????"+fx+"????":fl})
    return "????"+fx+"????"
########################################################################################
# get_variable_in_scope
#  proc_id : 0160
# argument : a global substitution variable name or a stacked variable name
#  purpose : find value of a global substitution name or a stacked variable name
#            convinient way to get check both in one routine
#  pre     : $gtree is properly inited, $gtree->{curr_tree} is set to the node currently being processed
#  post    : return the value of variable if found otherwise return null
########################################################################################
def __get_variable_in_scope(va,sub1=None,use_global=0):
    sub=sub1
    global __cached_dict__
    global gtree
    vb=None
    vc=None
    if va==None : return None
    if use_global: sub=__cached_dict__
    if sub==None : sub=gtree

    if debug_mode : print(va + " is passed in get_variable_in_scope")

    if assign_expr(None,re.match("\<\<\<\s*(\w+)\s*\>\>\>",va)): # if it is key name
        m=get_last_assign()
        return app_params.get(m.group(1))
    elif assign_expr(None,re.match("\#\#\#\s*(\w+)\s*\#\#\#",va)) : #if it is defined tree stack variable
        m=get_last_assign()
        vb=m.group(1)
        if debug_mode :
            print("going to pass "+vb+" into fetch_stacked_vars")
        __cached_dict__=sub
        return __fetch_stacked_vars(vb,None,use_global=1)
    elif assign_expr(None,re.match("^\s*(\w+)\s*$",va)) :
        m=get_last_assign()
        vb=m.group(1)
        if debug_mode2: print("bare word "+va+" is passed into get_variable_in_scope")
        __cached_dict__=sub
        return __fetch_stacked_vars(vb,None,use_global=1)
    elif assign_expr(None,re.match("\s*\#\#\#(\?\?\?\?REF\(\S+\)\?\?\?\?)\#\#\#\s*",va)) :
        m=get_last_assign()
        vb=m.group(1)
        if debug_mode: print("Here we are !!!!"+vb)
        #print "s1=$1,s2=$2,s3=$3,s4=$4,s5=$5 \nobject ref is detected, will trying get_func_ref\n" if ($debug_mode2);
        if debug_mode2 : print(m)
        __cached_dict__=sub
        return __fetch_stacked_vars(vb,None,use_global=1)
########################################################################################
# get_value_in_stack
#  proc_id : 0170
# argument : variable name & current gtree node
#  purpose : get variable from the gtree node only. Not from its ancesters or decendants
#            this is different from fetch_stacked_vars, the latter traverses all ancesters (still not for decendants)
#  pre     : $gtree is properly inited, $sub is the node to be accessed
#  post    : return null if the variable not in current node's stack
########################################################################################
def __get_value_in_stack(fl,sub1=None,use_global=0) :
    sub=sub1
    global __cached_dict__
    global gtree
    if use_global : sub=__cached_dict__
    if sub==None or fl==None : return
    return sub['stack'].get(fl)
########################################################################################
# push_stack_vars
#  proc_id : 0180
# argument : variable name & value & current gtree node
#  purpose : push variable to the stack of gtree node.
#  pre     : $gtree is properly inited, $sub is the node to be accessed
#  post    : the value in stack can be accessed
########################################################################################
def __push_stack_vars(fl,vl,sub1=None,use_global=0):
    sub=sub1
    if use_global : sub=__cached_dict__
    if sub==None:
        sub=__get_tree_by_tnid(gtree['curr_tnid'])
        if sub==None: sub=gtree
    sub['stack'].update({fl:vl})
    if debug_mode:
        print("pushed value of %s with %s to %s, gtree.curr_tree=%s, sub.parent=%s"%(fl,vl,sub['tnid'],gtree['curr_tnid'],gtree['parent_tnid']))
########################################################################################
# restore_value_in_stack
#  proc_id : 0190
# argument : variable name & value & current gtree node
#  purpose : restore the origin state of stack of the gtree node (undef it if neccessary)
#  pre     : $gtree is properly inited, $sub is the node to be accessed
#  post    : the old state of stack variable is restored
#  note    : at the moment, it is not saving/restoring the whole stack in one-call
########################################################################################
def __restore_value_in_stack(fl,vl,sub1=None,use_global=0):
    sub=sub1
    if use_global : sub=__cached_dict__
    if sub==None: return

    if vl==None: sub['stack'].pop(fl)
    else: sub['stack'][fl]=vl
########################################################################################
# fetch_variable
#  proc_id : 0200
# argument : global substitution variable name
#  purpose : get value of global substitution variable name
#  pre     : parse_template is called, get_variable_values is called
#  post    : return value found
#  note    : the name of this subroutine does not have "stacked"
########################################################################################
def __fetch_variable(key):
    m=re.match("^\s*(\w+)\s*$",key)
    value=None
    if (m) :
        value=app_params.get(key)
    else:
        m=re.match("^\!(\w+.+)\s+(\w+)\s*$",key)
        if (m) :
            cmdd=m.group(1)
            varr=m.group(2)
            if debug_mode : print("Found command "+cmdd+"for substitution variable [" + varr+ "]")
            value=app_params.get(varr)
        else:
            if debug_mode2 : print(c +" is not a proper variable name. Skip")

    #value=app_params.get(key)
    if debug_mode:
        print("substitute key : %s --> value:%s"%(key,value))
    if debug_mode and (value==None or value=="") :
        print("!!!!!! Couldn't find value for "+key+" !!!!!")
    return value;
########################################################################################
# __run_func
#  proc_id : 0210
# argument : function name and arguments
#           f=function name, p=parameter lists, orig=original line
#  purpose : to process tssml function
#  pre     : $gtree is properly inited
#  post    : process or call other utility subroutine accordingly
#  note    :
########################################################################################
def __run_func(f,p,orig=None):
    global __cached_dict__
    global ref_params
    global gtree
    global gsets
    global sub_depth
    global cls_defs

    if debug_mode:print("__run_func is called f=%s,p=%s,orig=%s"%(f,p,orig))
    if re.match(f,"\S+"):
        if debug_mode2: print("no function name is passed, return")
        return
    elif f=='define':      # func_001 : define
        if debug_mode: print("Defining local variables "+p)
        __parse_local_def(p)
        return
    elif f=='skip':        # func_002 : skip
        return
    elif f=='thru':        # func_003 : thru
        return p
    elif f=='mute':        # func_004 : mute
        return
    elif f=='ref' :        # func_005 : ref  # references stacked variable to global variable
        if assign_expr(None,re.match("^\s*(\w+)\s+(\w+)\s*$",p)) :
            m=get_last_assign()
            __cached_dict__=ref_params
            set_hash_value(None,m.group(1),'name',m.group(2)) # name = text, ref = object ref
        return # hide line from output
    elif f=='set' :        # func_006 : set
        __parse_var_assignment(p)
        return
    elif f=='get' :        # func_007 : {{{get}}}
        return __parse_var_retrieval(p)
    elif f=='push_hash' :  # func_008 : push_hash
        __push_local_hash_def(p)
        return # push hash will hide the line from output
    elif f=='iif' :        # func_009 : iif # if inline
        if debug_mode3 : print("p=%s in iff function"%(p))
        p=p.strip()
        tparr=shlex.split(p)
        tpvar=tparr[0]
        tplen=len(tparr)
        tpl="value="+tpvar
        m=0
        ret=''
        for j in range(1,tplen):
            if (j % 2 == 1) :
                if (j!=tplen-1):
                    tpl+=",ifmatch="+tparr[j]
                    if (tpvar == str(tparr[j])):
                        m=1
                else:
                    tpl+=",else="+tparr[j]
                    ret= tparr[j]
            else:
                tpl+=",return="+tparr[j]
                if m :
                    ret=tparr[j]
                    break
        if debug_mode3 : print("%s, ret=%s"%(tpl,ret))
        return ret
    elif f=='expr':        # func_010 : expr
        if debug_mode3 :
            print(">>Calling expr >>>>before reval , before translate expr is "+p)
        p=__translate_stacked_vars(p)
        p=__substitute_string(p)
        if debug_mode3:
            print(">>Calling expr >>>>before reval , after last translate expr is "+p)
        return reval_expr(p)
    elif f=='hash_keys' :  # func_011 : hash_keys
        if debug_mode : print("Calling hash_keys function p="+p)
        p=p.strip()
        pars=shlex.split(p)
        if debug_mode : print(f"pars={pars!r}")
        (hash,key1,key2,key3,key4,key5)=pack_list(pars,6)
        if debug_mode :
            print("1st: hash=%s,key1=%s,key2=%s,key3=%s,key4=%s"%(hash,key1,key2,key3,key4))
            __print_gtree()
        hash=__get_variable_in_scope(hash)
        key1=__get_variable_in_scope(key1)
        key2=__get_variable_in_scope(key2)
        if debug_mode : print("2nd: hash=%s,key1=%s,key2=%s,key3=%s,key4=%s"%(hash,key1,key2,key3,key4))
        if debug_mode: print(f"hash is {hash!r}")
        ret=None
        ret= get_hash_value(hash,key1,key2,key3,key4)
        if debug_mode: print(f"returning {ret}")
        return ret
    elif assign_expr(None,re.match("flat_list(_f|\s*)",f)) : # func_012 : flat_list
        m=get_last_assign()
        typ=m.group(1)
        if typ == '_f' :
            pars=shlex.split(p)
            (str1,dlm,func)=pars
            if debug_mode and verbose_mode:
                print("list is %s, delimiter is %s, function is %s"%(str1,dlm,func))
            if assign_expr(None,re.match("###(\S+)###",str1)) :
                m=get_last_assign()
                str1=m.group(1)
                lis=__fetch_stacked_vars(str1)
                #print "list is $list\n";
                if isinstance(lis,dict):
                    tar=lis.keys()
                    for idx in range(len(tar)-1) :
                        str1=tar[idx]
                        tar[idx]=__run_func(fuc,str1)
                    str1=",".join(tar)
                    if debug_mode : print("list is converted to string "+str1)
                elif isinstance(lis,list):
                    if debug_mode and verbose_mode:
                        print("it is array")
                else:
                    if debug_mode and verbose_mode : print("it is not ref")
                return str1
            elif assign_expr(None,re.match("<<<(\S+)>>>",str1)) :
                lis=__substitute_string(str1)
                lis=__fetch_stacked_vars(str1)
                print(f"list=$lis")
                if isinstance(lis,dict):
                    tar=lis.keys()
                    for idx in range(len(tar)-1):
                        str1=tar[idx]
                        tar[idx]=__run_func(fuc,str1)
                    str1=",".join(tar)
                elif isinstance(lis,list):
                    if debug_mode and verbose_mode:
                        print("it is array")
                else:
                    if debug_mode and verbose_mode:
                        print("it is not ref")
                return str1
    elif assign_expr(None,re.match("sub_(l|r)(\d+)",f)) :    # func_013,14 : sub_l|r
        m=get_last_assign()
        pos=m.group(1)
        len1=m.group(2)
        len1=0 if len==None else int(len1)
        print_s(["Here we are ",m,f,p,len1,pos],delim=':')
        if pos=='r' :
            len2=(0-len1)
            return substr(p,len2)
        else:
            return substr(p,0,len1)
    elif assign_expr(None,re.match("sub_m_(\d+)_(\d+)",f)) : # func_015 : sub_m
        m=get_last_assign()
        p1=m.group(1)
        p2=m.group(2)
        p1=int(p1)
        p2=int(p2)
        return substr(p,p1-1,p2-p1+1)
    elif assign_expr(None,re.match("pad_(t|s)(\d+)",f)):     # func_016,17 : pad_t|s
        m=get_last_assign()
        pos=m.group(1)
        len1=m.group(2)
        pp=[]
        if pos =='t' :
            pp.append(len1)
            pp.extend(shlex.split(p))
            return pad_t(pp)
        elif pos=='s' :
            pp.append(len1)
            pp.extend(shlex.split(p))
            return pad_s(pp)
        else:
            pp.apend(len1)
            pp.extend(shlex.split(p))
            return pad_s(pp)
    elif f=='lc' :                                           # func_018 : lc
        #print(f"lc of {p} is {p.lower()}")
        return None if p==None else p.lower()
    elif f=='uc' :                                           # func_019 : uc
        return None if p==None else p.upper()
    elif assign_expr(None, re.match("wrap_lst_(ht|st)(\d+)\Z",f)):  # func_020 : wrap_lst_st|st
        m=get_last_assign()
        opt=m.group(1)
        len2=m.group(2)
        if debug_mode:
            print("%s: parameter passed in :  %s opt=%s,len=%s\n"%(f,p,opt,len2))
        if opt=='ht':
            if assign_expr(None,re.match("(.*)(ARRAY\(0x\w+\))(.*)",p)) :
                m=get_last_assign()
                astr=m.group(2)
                aref=arr_refs.get('astr')
                result=None
                ttp=None
                if debug_mode and isinstance(aref,dict) : print("Detect array ref "+aref)
                for al in aref :
                    ttp=p
                    if debug_mode : print("al=%s,p=%s,astr=%s"%(al,p,astr))
                    al=pad_s(int(len2),al)
                    ttp=re.sub(astr,al,ttp)
                    #$ttp =~ s/\Q$astr/$al/;
                    result+=ttp+"\n"
                result=chomp(result)
                return result
        else:
            print("**** Error ! Unknown function name "+f+" !!!!!")
    elif re.match("^(\#|comment|\*|\-\-)$",f):              # func_021 :  # comment
        return # this is comment, skip
    elif re.match("diff_update",f):                     # func_018 :  # diff_update
        if debug_mode :
            print("to diff_update a file %s, orig=%s, sub_depth=%s"%(p,orig,sub_depth))
        nlines,olines,ulines=None,None,None

        template=gsets['template_selected']
        cwd=gsets['cwd']
        target=gsets['target']
        dirname=gsets['template_dir']

        if sub_depth!=0 :
            print("**** Error! diff_update can only be used for file name substitution not file content.")
            quit()
        if debug_mode:
            print("source file is %s/%s/{{{%s}}}"%(dirname,template,orig))

        ret=exit_when_not_found(path.join(target,p),1)

        if ret:
            print("Skip.")
            sub_depth=-2
            return

        FS = open(path.join(dirname,template,"\{\{\{"+orig+"\}\}\}"), "r")
        nlines=FS.readlines()
        FS.close()

        FT = open(path.join(target,p), "r")
        olines=FT.readlines()
        FT.close()

        print(f"Comparing files and update if required...")

        for tl1 in nlines :
            tl=__substitute_string(tl1)
            if debug_mode :
                print(f">>> comparing {tl}")
            m=0
            for tl2 in olines :
                if tl == tl2 :
                    m=1
                    if debug_mode : print("line exists, skip")
            if debug_mode and m==0:
                print(f"found new line {tl}")
            if m==0 :
                ulines.append(tl)

        FU = open(path.join(target,p),'w')
        if len(ulines)>0 :
            FU.write("##################################################\n")
            FU.write("##### Below lines are added by menusetup.pl ######\n")
            FU.write("##################################################\n")

            for ul in ulines :
                if debug_mode :
                    print(f"writing {ul}")
                FU.write(f"{ul}\n")
            print(f"write {len(ulines)} lines into {path.join(target,p)}\n")
        else:
            print(f"No new line was found and hence none was written to {path.join(target,p)}")
        FU.close()
        sub_depth=-1
        return
    elif f == 'fi_writefile' : # func_023
        if debug_mode : print(f"fi_writefile params={p}, orig={orig}, sub_depth={sub_depth}")

        gi_startpos=0
        m=None
        gi_src=''
        gi_tgt=''
        gi_args=''
        tpl_dir=gsets['template_dir']
        tpl_selected=gsets['template_selected']

        if assign_expr(None,re.match("source=(.*);target=(.*);args=(.*)",p)):
            m=get_last_assign()
            gi_src=path.join(tpl_dir,tpl_selected,(m.group(1)))
            gi_tgt=m.group(2)
            gi_args=m.group(3)
            if debug_mode : pgroups(m,5,1,1,"p-groups")
            if gi_args!=None:
                arr1=re.split(';',gi_args)
                #print(f"arr1={arr1!r}")
                gi_args=arr1[0]
                if len(arr1)>1 :
                    m=re.search("startpos\s*=\s*(\d+)(\s|$)",arr1[1])
                    if m.group(1)!=None: gi_startpos=m.group(1)
            if debug_mode : print(f"source={gi_src},target={gi_tgt},args={gi_args},startpos={gi_startpos}")
            FS = open(gi_src, "r")
            olines=FS.readlines()
            if gi_startpos!=0 :
                olines=olines[int(gi_startpos):]
            FS.close()
            nlines=[];
            gtree['nlines']=None
            gtree['nlines']=nlines
            if debug_mode and verbose_mode: print(f"Before processing, nlines={nlines!r}")
            __init_gtree(olines)
            gtree['file_args']=gi_args
            if debug_mode : __print_gtree()
            __process_file_content(olines)
            nlines=gtree['nlines']
            if debug_mode and verbose_mode : print(f"After processing, nlines={nlines!r}")
            print(f"Creating {gi_tgt}")
            FH = open(gi_tgt,"w")
            for tgll in nlines:
                FH.write(tgll+"\n")
            FH.close()
            implement_fo(gtree,gi_tgt)
            clear_fo(gtree)
            print("Complete.")
        else:
            print(f"Invalid Argument gi_writefile:{p}\n")
    elif re.match("get_args",f) :  # func_024 : get_args
        args=gtree.get('file_args')
        if len(args)>0 :
            __parse_local_def(p)
            arr=shlex.split(args)
            tarr=shlex.split(p)
            for tl in range(len(tarr)) :
                if verbose_mode: print("loading argument %s with value %s"%(tarr[tl],arr[tl]))
                __push_stack_vars(tarr[tl],arr[tl])
    elif f =='fo_chmod'  :  # func_25 : fo_chmod
        __cached_dict__=gtree
        set_hash_value(None,'file_options','chmod',p)
        return
    elif f == 'range'    :  # func_26 : range
        if assign_expr(None,re.match("^\s*(\d+)\s*\.\.\s*(\d+)\s*$",p)) :
            aar=range(m.group(1),m.group(2))
            return aar
        else:
            aar=re.split(",",p)
            return aar
    elif f == 'contains' :  # func_27 : check exisitence of array or hash elements
        if debug_mdoe : print(f"Calling in_list function p={p}")
        p=p.strip()
        pars=re.split("\s+",p)
        if len(pars)<2:
            print(f"*** Error : Missing arguments for {f}, need two")
            return 0
        pouch=pars[1]
        checker=pars[0]
        if debug_mode:
            print(f"1st: checker={checker} pouch={pouch}")
        checker=__get_variable_in_scope(checker)
        pouch=__get_variable_in_scope(pouch)
        if debug_mode:
            print(f"2nd: checker={checker} pouch={pouch}")
            print(f"checker is {checker}")

        if isinstance(pouch,list) :
            if checker in pouch :
                return 1
        elif isinstance(pouch,dict):
            ckk=get_hash_value(pouch,checker);
            if ckk==None : return 1
        return 0
    elif f == 'fields'   :  # func_29 :
        pars=re.split("\s+",p)
        fdef=pars[0]
        dlm=pars[1]
        dlm2=pars[2]
        date=" ".join(pars[3:])
        arr=()
        farr=re.split(',',fdef)
        if dlm == '[space]':
            arr=re.split("\s+",dat)
        else:
            arr=re.split(dlm,dat)

        str1=''
        for i in farr:
            str1+=arr[i]
            if dlm2 == '[space]':
                str1+=' '
            else:
                str1+=dlm2
        return str1[:-1]
    elif assign_expr(None,re.match("\s*(\w+)\.(\w+)\s*$",f)) : #2nd to last : class method
        m=get_last_assign()
        if debug_mode :
            print(f"class method is called {f}")
        objn=m.group(1)
        mth=m.group(2)
        return __translate_class_method(objn,mth,p,orig)
    else: # func_user_defined : here is the interface to call user-defined subroutine, add your function above this line
        hash=sub_defs.get(f)
        if hash!=None :
            ptr=hash.get['r']
            if  ptr!=None :
                #if debug_mode3: print("need to pass argument to $ptr:$ptr->{var} and run")
                nlines=[]
                olines=ptr.get('raw_lines')
                old_gtree=gtree
                curr_tree=get_tree_by_tnid(gtree['curr_tnid'])
                curr_node=gtree['current_node']
                sub=gtree['nodes'].get('curr_node')
                gtree={}
                gtree['nlines']=nlines # to save result lines
                __init_gtree(olines)
                for tline in olines:
                    __explore_file_line(tline)

                argdefs=ptr.get('arglist')
                args=shlex.split(p)
                for kk in range(len(argdefs)):
                    __push_stack_vars(argdefs[kk],args[kk],gtree)
                __translate_tree(gtree)
                nlines=gtree['nlines']
                sub['nodes']=gtree['nodes']
                gtree=old_gtree
                if debug_mode3:
                    print("about to attach the translated lines to current node of [%s], nid=%d\n"%(gtree['curr_tnid'],gtree['current_node']))
                return "\n".join(nlines)
            else:
                print("**** Error ! subroutine "+f+" definition is found, but its body is invalid")
                return
        print("**** Error ! Unknown function name "+f+" !!!!!")
    return p
########################################################################################
# translate_class_method
#  proc_id : 0211
# argument :
#  purpose : translate class method calls
#  pre     : $gtree is properly inited, $cls_def is parsed, class object is properly instantiated
#  post    :
#  note    :
########################################################################################
def __translate_class_method(objn,mth,p,orig):
    global gtree
    global cls_defs
    global sub_defs
    global __cached_dict__
    global ___prev_tl

    if debug_mode:
        print(f"fetching obj {objn} from stack")
    # find the object from stack

    hash,objstack,objsuper,clssuper,obj=None,None,None,None,None

    if objn=='super': # must inside a class instance and hence gtree is class context
        #walk_dict(gtree,1,1,'highly suspect')
        obj=gtree.get('super')
        if (obj == None) :
            print(f"**** Error! Super class does not exist, cannot call its super.{mth} method.")
            return f"{obj}.{mth}"
    else:
        tnid=gtree['curr_tnid']
        curr_tree=__get_tree_by_tnid(tnid)
    obj=__fetch_stacked_vars(objn,curr_tree)
    if debug_mode3 and verbose_mode and obj!=None:
        walk_dict(obj,1,1,"fetched class instance")
    if (obj==None) :
        print(f"**** Error! Unknown object {objn}, cannot call its method.")
        return orig

    __cached_dict__=obj
    hash=get_hash_value(None,'methods',mth)
    __cached_dict__=obj
    objstack=get_hash_value(None,'r','stack')
    __cached_dict__=obj
    objsuper=get_hash_value(None,'r','super')
    __cached_dict__=obj
    clssuper=get_hash_value(None,'r','superclass')

    #print("hash=$hash, objstack=$objstack, objsuper=$objsuper, clssuper=$clssuper\n");
    #walk_dict($obj,1,1,"obj is ");
    while hash==None:
        #print("hash=$hash, objstack=$objstack, objsuper=$objsuper\n");
        if (objsuper==None) :
            break
        obj=objsuper
        __cached_dict__=obj
        hash=get_hash_value(None,'methods',mth)
        __cached_dict__=obj
        objstack=get_hash_value(None,'r','stack')
        __cached_dict__=obj
        objsuper=get_hash_value(None,'r','super')

    if hash !=None:
        ptr=hash.get('r')
        if ptr!=None:
            if debug_mode: print(f"need to pass argument to {ptr}:{ptr.get('var')} and run")
            nlines=[]
            olines=ptr.get('raw_lines')
            old_gtree=gtree
            tnid=gtree['curr_tnid']
            curr_tree=__get_tree_by_tnid(tnid)
            curr_node=gtree.get('current_node')
            __cached_dict__=getree
            sub=get_hash_value(None,'nodes',curr_node)
            gtree={}
            gtree['nlines']=nlines
            __init_gtree(olines)
            gtree['stack']=objstack # the stack should be copied for class object instance
            gtree['type2']=obj.get('type2')
            gtree['super']=objsuper if objsuper!=None else None
            if debug_mode:
                walk_dict(gtree['super'],1,1,"super here is ")

            for tline in olines:
              __explore_file_line(tline)
              ___prev_tl=tline

            argdefs=ptr.get('arglist')
            args=re.split("\s+",p)
            for kk in range(0,len(argdefs)) :
                __push_stack_vars(argdefs[kk],args[kk],gtree)
            __translate_tree(gtree)

            nlines=gtree.get("nlines")
            sub['nodes']=gtree['nodes']
            gtree=old_gtree
            if debug_mode3:
                print(f"about to attach the translated lines to current node of {gtree['curr_tree']!r},{get_hash_value(gtree,'curr_tree','type')}, curr_tree={curr_tree!r}, nid={curr_node}")
            return "\n".join(nlines)
        pass
    else:
        print(f"**** Error ! Unknown method {mth} for {objn}")
########################################################################################
# instantiate_cls
#  proc_id : 0212
# argument :
#  purpose : instantiate a new object as specified by class name
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it
#  post    :
#  note    :
########################################################################################
def __instantiate_cls(seeker):
    global gtree
    global cls_defs
    try:
        clsdef=cls_def[seeker];
    except KeyError:
        return None
    clsdef['classname']=seeker
    if debug_mode : print(f"clsdef of {seeker} is {clsdef!r}")
    if clsdef != None :
        if debug_mode : walk_dict(clsdef,1,1,"Found class def")
        __trace_ancester_cls(clsdef)
        obj=deepcopy(clsdef)
        if debug_mode:
            print(f"class def is {clsdef!r}, instantiated obj is {obj!r}")
            walk_dict(obj,1,1,"found class def")
        return obj
    return None
########################################################################################
# trace_ancester_cls
#  proc_id : 0213
# argument :
#  purpose : worker subroutine for instantiate_cls to trace all super classes
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it
#  post    :
#  note    :
########################################################################################
def __trace_ancester_cls(seeker):
    global gtree
    global __cached_dict__
    if seeker==None: return seeker
    superclsn=get_hash_value(seeker,'r','superclass')
    if superclsn==None : return seeker
    supercls=None
    try:
        supercls = clsdef['superclsn']
    except KeyError:
        supercls=None
    if supercls==None :
        print(f"**** Error ! cannot inherit superclass {superclsn} for {seeker}\n");
    __trace_ancester_cls(supercls)
    set_hash_value(seeker,'r','super',supercls)
    return seeker
########################################################################################
# set_class_obj_stack_var
#  proc_id : 0214
# argument :
#  purpose : assign value to object property
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it
#  post    :
#  note    :
########################################################################################
def __set_class_obj_stack_var(obj,vname,value) :
    global __cached_dict__
    if obj==None : return
    objstack=get_hash_value(obj,'r','stack')
    __cached_dict__=objstack
    set_hash_value(None,vname,value)
########################################################################################
# set_class_obj_stack_var
#  proc_id : 0215
# argument :
#  purpose : retrieve value to object property
#  pre     : $gtree is properly inited, $cls_def is properly parsed which has the class definition in it
#  post    :
#  note    :
########################################################################################
def __get_class_obj_stack_var() :
    pass
########################################################################################
# parse_local_def
#  proc_id : 0220
# argument :
#  purpose : parse {{{define ....}}} function, and extract array definition and those with intial values
#  pre     : $gtree is properly inited
#  post    :
#  note    : currently only process array intial values
########################################################################################
def __parse_local_def(f):
    global gtree
    global __cached_dict__
    if debug_mode: print("Parsing local def "+f)
    if assign_expr(None,re.match("^(.*)\s*(^|\,|\s)(\w+)\s*\=\s*(\(([a-zA-Z][\w|\,]*)\))(.*)$",f)) :
        m=get_last_assign()
        if debug_mode and verbose_mode :
            #print "Find Array definition s1=$1,s2=$2,s3=$3,s4=$4,s5=$5,s6=$6\n" if ($debug_mode && $verbose_mode);
            print("match object is "+str(m))
        h=m.group(1)
        t=m.group(6)
        var=m.group(3)
        c=m.group(5)
        arr=re.split(',',c)
        if debug_mode:
            print("gtree is "+gtree['tnid'])
            print("gtree->curr_tree is "+gtree['curr_tnid'])
            print_s(["inited array length is ",arr])
            print("pushing array "+var+" into stack")

        curr_tree=get_tree_by_tnid(gtree['curr_tnid'])

        if curr_tree==None or curr_tree==gtree :
            gtree['stack'].update({var:arr})
        else:
            curr_tree['stack'].update({var,arr})
    elif assign_expr(None,re.match("^\s*(\w+)(\s+$|\s*$|\s*=\s*(.*)$)",f)) :
        # old combination f=~/^\s*(\w+)\s*=\s*(.+)\s*$/ + $=~/^\s*(\w+)\s*$/
        m=get_last_assign()
        var=m.group(1)
        rem=m.group(3)
        if debug_mode:
            print("literal variable if detected.")
            print("gtree is "+gtree['tnid'])
            print("gtree->curr_tree is "+gtree['curr_tnid'])

        curr_tree=get_tree_by_tnid(gtree['curr_tnid'])

        if curr_tree==None or curr_tree==gtree :
            gtree['stack'].update({var:rem})
        else:
            curr_tree['stack'].update({var,rem})
    elif assign_expr(None,re.match("^\s*(\w+)\s+as\s+(\w+)$",f)) : # class definition, instantiate and push to stack
        m=get_last_assign()
        var=m.group(1)
        clsdef=m.group(3)
        if debug_mode :
            print("gtree is "+gtree['tnid'])
            print("gtree->curr_tree is "+gtree['curr_tnid'])
            print(f"instantiate class object {var} as {clsdef!r}")
            print(f"pushing variable {var} into stack")
        obj=__instantiate_cls(clsdef)
        if obj!=None:
            print(f"**** Error ! Unknowns class {clsdef}, cannot instantiate")

        if curr_tree==None or curr_tree==gtree :
            gtree['stack'].update({var:obj})
        else:
            curr_tree['stack'].update({var,obj})
########################################################################################
# push_local_hash_def
#  proc_id : 0230
# argument :
#  purpose : parse {{{push_hash ....}}} function, and extract hash definition
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
def __push_local_hash_def(p):
    global gtree
    if assign_expr(None,re.match("\s*(\w+)\s+(\w+)\s+(.+)$",p)) :
        hash=m.group(1)
        key=m.group(2)
        rv=m.group(3)
        if (debug_mode or debug_mode2):
            print("pushing value %s with key=%s to %s"%(rv,key,hash))
        if assign_expr(None,re.match("^\s*\(([\s|\w|\,]+)\)\s*$",rv)): # pushing array
            m=get_last_assign()
            dv=m.group(1)
            dv=re.split(',',dv)
            if debug_mode:
                print("about to push data into %s with %s"%(hash,dv))
            tree=None
            curr_tree=get_tree_by_tnid(gtree['curr_tnid'])
            if (curr_tree==None or curr_tree==gtree ) :
                tree=gtree
            else:
                tree=curr_tree
            if tree==None : return
            hashref=tree['stack'].get(hash)
            if hashref!=None :
                global __cached_dict__
                __cached_dict__=tree
                set_hash_value(None,'stack',hash,key,dv)
            else:
                hashref[key]=dv
            if debug_mode and verbose_mode:
                print("hashref is located , "+hashref+", data is pushed : "+dv )
    else:
        return("Invalid function call: "+p)
########################################################################################
# parse_var_assignment
#  proc_id : 0240
# argument :
#  purpose : parse {{{push_hash ....}}} function, and extract hash definition
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
def __parse_var_assignment(f) :
    global gtree
    global __cached_dict__
    if debug_mode: print(f"Parsing var assignment statement {f}")

    if assign_expr(None,re.match("^\s*(\S+)\s*=(.+)$",f)):
        m=get_last_assign()
        vname=m.group(1)
        value=m.group(2)
        if value!=None: value=value.strip()
        if re.search("{{{|}}}|###|<<<|>>>",value):
            value=__translate_stacked_vars(value)
            value=__substitute_string(value)

        if assign_expr(None,re.match("^\s*(\w+)\.(\w+)\s*$",vname)) :
            m=get_last_assign()
            objn=m.group(1)
            vname=m.group(2)
            if debug_mode:
                print(f"found object assignment statement for {objn}")
                print(f"fetching obj {objn} from stack")
            # find the object from stack
            obj=__fetch_stacked_vars(objn,gtree['curr_tree'])
            if debug_mode3 and verbose_mode and obj!=None:
                walk_dict(obj,1,1,"fetched class instance")
            if obj!=None:
                print(f"**** Error! Unknown object {objn}, cannot call its method.")
                return f
            __set_class_obj_stack_var(obj,vname,value)
        else:
            if debug_mode : print(f"pushing stack var {vname}={value}")
            __push_stack_vars(vname,value)
    else:
        print(f"**** Error ! Invalid assign statement : {f}")
########################################################################################
# parse_var_retrieval
#  proc_id : 0241
# argument :
#  purpose : parse variable retrieval if is has any dynamic part
#  pre     : $gtree is properly inited
#  post    :
#  note    :
########################################################################################
def __parse_var_retrieval(f):
    global gtree
    global __cached_dict__
    if debug_mode : print(f"Parsing var get statement {f}")
    if assign_expr(None,re.match("^(.+)$",f)):
        m=get_last_assign()
        vname=m.group(1)
        max=100
        ## keep translate until it is all drained out
        while re.search("{{{|}}}|###|<<<|>>>",vname) and max>0 :
            vname=__translate_stacked_vars(vname)
            vname=__substitute_string(vname)
            max-=1
        if assign_expr(None,re.match("^\s*(\w+)\.(\w+)\s*$",vname)) :
            m=get_last_assign()
            objn=m.group(1)
            vanme=m.group(2)
            if debug_mode:
                print(f"found object assignment statement for {objn}")
                print(f"fetching obj {objn} from stack")
            # find the object from stack
            __cached_dict__=gtree
            obj=__fetch_stacked_vars(objn,get_hash_value(None,'curr_tree'))
            if debug_mode3 and verbose_mode and obj!=None:
                walk_dict(obj,1,1,"fetched class instance")
            if obj==None:
                print(f"**** Error! Unknown object {objn}, cannot call its method.")
                return f
            __get_class_obj_stack_var(obj,vname)
        else:
            return __fetch_stacked_vars(vname)
    else:
        print(f"**** Error ! Invalid get statement : {f}")
######### miscellaneous subroutines ##############
#######################################################
## type 2 universal utility subroutines
#######################################################
def pad_s(params) :
    plen=int(params[0])
    output=''

    if (params==None or len(params)<=1) :
        return params
    else:
        i=1
        while i < len(params) :
            output += params[i]
            i+=1
        output=output.rstrip()
        plen2=len(output)

        return output + (' ' * (plen - plen2));
    pass
def pad_t(params) :
    h=pad_string(params)
    if len(params)<=1 :
        return params
    else:
        plen=int(params[0])
        plen2=len(h)
        rem=plen-plen2
        id1=1
        id2=len(params)-1
        a1=0
        a2=0
        h1=''
        h2=''
        #print "rem=$rem\n";
        while a2<= rem :
           #if debug_mode2: print("a1=%d,a2=%d,rem=%d,id1=%d,id2=%d,plen=%d,plen2=%d,h=%s"%(a1,a2,rem,id1,id2,plen,plen2,h))
           h2+=h1
           a2=len(h2)
           #print(params)
           #print(id1)
           h1=params[id1]
           id1+=1
           a1=len(h1)
           a2+=a1

           #print "h1=$h1,h2=$h2,a1=$a1,a2=$a2\n";
           if (a1==0 or id2>id1) : break
           h1+=" "

        h2=h2.rstrip()
        return h + h2 + ' ' * (plen - plen2 - len(h2))
    return
def pad_string(params) :
    #print(params)
    if len(params)<=1 :
        return params
    else:
        plen=int(params[0])
        rem,cnt,len2=0,0,0
        tts=''
        mx=len(params)
        idx=1
        for mt in params[1:mx] :
            tts+=str(mt)+" ";
        tts=tts.rstrip()
        plen2=len(tts)
        cnt=floor(plen/plen2)
        rem=plen-cnt*plen2;
        return tts + tts * cnt
def reval_expr(confined_code) :
    result = eval(confined_code)
    if (debug_mode and verbose_mode) : print("result="+str(result)+" in reval_expr")
    return result
def split_q(delim,strr,keep_quote=0):

    m=re.match("^([^\"]*)\"([^\"]*)\"(.*)$",strr)
    if not m: return re.split(delim,strr) # do as normal because of double-quoations in the string

    # contains string with double-quoations
    h=m.group(1)
    c=m.group(2)
    t=m.group(3)

    m=re.match("^\s*"+delim+"(.*)$",t)
    if (m): t=m.group(1)
    arr1=None
    arr2=None
    if keep_quote: c="\""+c+"\""

    m=re.match("(.+)"+delim+"(((?!"+delim+").)*)",h)
    if (m) :
    # if leadning substring contains non-empty script after last delimiter
        c=m.group(2)+c
        h=m.group(1)
        if h==None: arr1=[c]
        else:
            arr1=re.split(delim,h)
            len1=len(arr1)
            arr1=arr1+[c]
    else:
        arr1=re.split(delim,h)
        len1=len(arr1)
        if len1==0 : arr1=[c]
        elif len1==1 : arr1=[arr1[0]+c]
        elif len1==2 : arr1=[arr1[0]]+[arr1[1]+c]
        else :arr1=arr1[0:len1-2]+[arr1[len1-1]+c]

    if t==None : return arr1

    arr2=split_q(delim,t,keep_quote)

    if debug_mode : print("!!!!!!!!!!!!!!!!!!! t="+t+"  arr2="+str(arr2))

    len1=len(arr1)
    len2=len(arr2)

    if len2==0 : return arr1
    if len1==0 : return arr2

    #if (len1==1):
    #    arr1=[arr1[0],arr2[0]]
    #elif (len1==2):
    #    arr1=[arr1[0],arr1[1]+arr2[0]]
    #else : arr1=arr1[0:len1-2]+[arr1[len1-1]+arr2[0]]

    return arr1+arr2
def fmt_banner(title) :
    wid=preview_banner_width
    head="+"+"-" * (wid-2) + "+"
    fmt =f"{head}\n"
    fmt+="| "+ pad_s([wid-4,title])+" |\n"
    fmt+=f"{head}\n"
    return fmt
def fmt_splitter(wid=0):
    if wid<=2:
        wid=preview_banner_width
    head="+"+"-" * (wid-2) + "+"
    return head

#######################################################
## type 3 Python specific utility subroutines -- maily to mimic functionality of perl
#######################################################
#  repercussion 1.2.1.b.6
def replace_none_with_space(vlist):
    if vlist==None: return ('');
    sz=len(vlist)
    #print(f"size of vlist is {sz}")
    ret=()
    for i in range(sz):
        if vlist[i]==None:
            ret=ret + ('',)
        else:
            ret=ret + (vlist[i],)
    #print(f"returning ret={ret}")
    return ret
def pack_list(vlist, count=0, use_original=0) :
    if count<=0:
        return vlist;
    else :
        lst=[]
        if vlist==None:
            for i in range(count):lst.append(None)
            return lst;
        else:
            ll=len(vlist)
            if (use_original):
                for i in (ll,count):vlist.append(None)
                return vlist
            else:
                for i in range(ll): lst.append(vlist[i])
                for j in range(ll,count): lst.append(None)
                return lst
def get_hash_value(hash,key1,key2=None, key3=None, key4=None, key5=None, key6=None, key7=None) :
    if debug_mode and verbose_mode : print(f"getting value by key={key1}")
    if hash==None : return None
    obj=hash.get(key1)
    if key2==None  : return obj
    return get_hash_value(obj,key2,key3,key4,key4,key6,key7)
def set_hash_value(hash,kv1,kv2=None,kv3=None,kv4=None,kv5=None,kv6=None,kv7=None,kv8=None,kv9=None,flag=0) :
    global __cached_dict__
    if debug_mode :print("k1=%s,k2=%s,k3=%s,k4=%s"%(kv1,kv2,kv3,kv4))

    if hash!=None : __cached_dict__=hash
    if __cached_dict__==None : return None
    if kv1==None : return __cached_dict__

    tmp=None
    try:
        tmp=__cached_dict__[kv1];
    except KeyError:
        __cached_dict__.update({kv1:{}})

    if kv2==None : return hash if hash!=None else __cached_dict__
    tmp=__cached_dict__[kv1]

    if isinstance(tmp,dict) :
        if (kv3==None): __cached_dict__[kv1]=kv2
        arr=tmp.items();
        if len(arr)==0 : __cached_dict__[kv1]=kv2
    else :
        if kv3==None : __cached_dict__[kv1]=kv2

    if kv3==None : return hash if hash!=None else __cached_dict__

    try:
        tmp=__cached_dict__[kv1]
    except KeyError:
        __cached_dict__[kv1]={}

    if not isinstance(tmp,dict) :
        __cached_dict__.update({kv1:{kv2:kv3}}) # convert it to dict
    else:
        if kv4==None : __cached_dict__[kv1].update({kv2:kv3})

    if kv4==None : return hash if hash!=None else __cached_dict__

    try:
        tmp=__cached_dict__[kv1][kv2]
    except KeyError:
        __cached_dict__[kv1][kv2]={}

    if not isinstance(tmp,dict) :
        __cached_dict__[kv1].update({kv2:{kv3:kv4}})
    else:
        if kv5==None : __cached_dict__[kv1][kv2].update({kv3:kv4})

    if kv5==None : return hash if hash!=None else __cached_dict__
    try:
        tmp=__cached_dict__[kv1][kv2][kv3]
    except KeyError:
        __cached_dict__[kv1][kv2][kv3]={}

    if not isinstance(tmp,dict) :
        __cached_dict__[kv1][kv2].update({kv3:{kv4:kv5}})
    else:
        if kv6==None : __cached_dict__[kv1][kv2][kv3].update({kv4:kv5})

    if kv6==None : return hash if hash!=None else __cached_dict__
    try: tmp=__cached_dict__[kv1][kv2][kv3][kv4]
    except KeyError: __cached_dict__[kv1][kv2][kv3][kv4]={}
    if not isinstance(tmp,dict) :
        __cached_dict__[kv1][kv2][kv3].update({kv4:{kv5:kv6}})
    else:
        if kv7==None : __cached_dict__[kv1][kv2][kv3][kv4].update({kv5:kv6})

    if kv7==None : return hash if hash!=None else __cached_dict__
    try: tmp=__cached_dict__[kv1][kv2][kv3][kv4][kv5]
    except KeyError:__cached_dict__[kv1][kv2][kv3][kv4][kv5]={}
    if not isinstance(tmp,dict) :
        __cached_dict__[kv1][kv2][kv3][kv4].update({kv5:{kv6:kv7}})
    else:
        if kv8==None : __cached_dict__[kv1][kv2][kv3][kv4][kv5].update({kv6:kv7})

    if kv8==None : return hash if hash!=None else __cached_dict__
    try: tmp=__cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6]
    except KeyError: __cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6]={}
    if not isinstance(tmp,dict) :
        __cached_dict__[kv1][kv2][kv3][kv4][kv5].update({kv6:{kv7:kv8}})
    else:
        if kv9==None : __cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6].update({kv7:kv8})

    if kv9==None : return hash if hash!=None else __cached_dict__
    try:tmp=__cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6][kv7]
    except KeyError:__cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6][kv7]={}
    if not isinstance(tmp,dict) :
        __cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6].update({kv7:{kv8:kv9}})
    else:
        __cached_dict__[kv1][kv2][kv3][kv4][kv5][kv6][kv7].update({kv8:kv9})

    return hash if hash!=None else __cached_dict__
def chomp(line) :
    if (line==None) : return
    a=re.split("\n",line);
    a=re.split("\r",a[0]);
    a[0]=a[0].strip()
    return a[0];
def concat(arr,delim=None) :
    if arr==None : return ""
    ret=""
    for ak in arr :
        if ak==None :
            if delim!=None: ret+=delim
            continue
        else:
            if isinstance(ak,str):
                ret+=ak if delim==None else ak+delim
            else:
                ret+=str(ak) if delim==None else str(ak)+delim
    if delim!=None : ret=ret.rstrip(delim)
    return ret
def print_s(arr,delim=None):
    if (arr)==None: print("")
    else:
        print(concat(arr,delim))
def print_f(s,arr) :
    pass
def substr (str1,pos,length=None):
    if debug_mode and verbose_mode : print_s(["substr is called :",str1,pos,length])
    if str1==None :return
    alen=len(str1)
    pos1=pos
    if pos1<0 :
        pos1=alen+pos1
    pos2=alen
    if length!=None: pos2=pos1+length
    #print_s([pos1,pos2],":")

    return str1[pos1:pos2]
def pgroups (mobj,maxgrps=20,prt_flg=1,hide_ref=1,prt_title=None):
    fmt=""
    if prt_title !=None :
        fmt=fmt_banner(prt_title)
    if mobj==None : return fmt
    if not hide_ref :
        fmt+=f"m={mobj!r}\n"
    try:
        for idx in range(1,maxgrps) :
            fmt += f"[group {idx!s}={mobj.group(idx)!s}] "
    except:
       fmt +=";"
    if (prt_title!=None):
        fmt+="\n"+fmt_splitter()
    if (prt_flg) : print(fmt)
    return fmt

#######################################################
## type 1 TSSML functionality utility subroutines
#######################################################
def __find_nested_pairs(s,e,hash):
    pass
def __find_match(s,e,str1):
    if debug_mode : print(f"str1={str1},s={s},e={e}")
    if str1==None : return -1
    pos1=str1.find(s)
    pos2=str1.find(e)
    if debug_mode and verbose_mode: print(f"pos1={pos1}, pos2={pos2}")
    if pos2==-1 : # not found
        return -1
    elif pos1==-1 :
        return pos2
    elif pos1>=pos2 :
        return pos2
    else:
        return pos2+len(e)+__find_match(s,e,substr(str1,pos2+len(e)))
def __find_first_collection(str1):
    if debug_mode and verbose_mode : print(f"__find_first_collection arg1:{str1}")

    pos1= str1.find('{{{')
    pos2= str1.find('<<<')

    if pos1>=0 and pos1<pos2:
        if assign_expr(None,re.match("(((?!\{\{\{).)*)\{\{\{(((?!\}\}\}).)*)\}\}\}(.*)",str1)) :
            m=get_last_assign()
            if debug_mode : pgroups(m,10,1,1,"collection type=func,searching first collection")
            h=m.group(1)
            c=m.group(3)
            t=m.group(5)
            return [len(h),'h',c,t]
        pass
    else:
        if assign_expr(None,re.match("(((?!<<<).)*)<<<(((?!>>>).)*)>>>(.*)",str1)) :
            m=get_last_assign()
            if debug_mode: pgroups(m,10,1,1,"collection type=s,searching first collection")
            h=m.group(1)
            c=m.group(3)
            t=m.group(5)
            return [len(h),'s',c,t]
        pass
    pass
def is_muted(key) :
    global muted_params
    h=muted_params.get(key)
    return 1 if h!=None else 0
def __print_params(p=None) :
    wid=preview_banner_width
    head="+"+"-" * (wid-2) + "+"
    print(head)

    if (p=='raw') :
        print("| "+ pad_s([wid-4,"Substitution variables found in template files"])+" |")
        print(head)
        walk_dict(raw_params,1)
    else:
        print("| "+ pad_s([wid-4,"All substitution variables and values"])+" |")
        print(head)
        walk_dict(app_params,1)
    print(head)
    return
def walk_dict(d,depth=0,hide_list=1,title=None):
    head=''
    #print(d)
    if title!=None :
        wid=preview_banner_width
        head="+"+"-" * (wid-2) + "+"
        print(head)
        print("| "+pad_s([wid-4,title])+" |")
        print(head)
    if d==None :
        print("  " * depth + " None ")
        return
    for k,v in sorted(d.items(),key=lambda x: x[0]):
        if isinstance(v, dict):
            print("  "*depth + ("+[ %s ]" % k))
            walk_dict(v,depth+1)
        else:
            if hide_list and isinstance(v,list) :
                print ("  " * depth + " [ %s ] = [ %s ]" % (k, "list of "+str(len(v))+" elements"))
            else:
                print ("  " * depth + " [ %s ] = [ %s ]" % (k, v))
    if title!=None :
        print(head)
def set_gtree_value(kv1,kv2=None,kv3=None,kv4=None,kv5=None,kv6=None,kv7=None,kv8=None,kv9=None,) :
    global __cached_dict__
    global gtree
    __cached_dict__=gtree
    set_hash_value(None,kv1,kv2,kv3,kv4,kv5,kv6,kv7,kv8,kv9)
def __element_to_sub_hash(hash,key1) :
    global __cached_dict__
    if hash!=None : __cached_dict__=hash
    if __cached_dict__==None : return {key1:None}
    try:
        elem=__cached_dict__[key1]
    except KeyError:
        __cached_dict__.update({key1:{}})
        return __cached_dict__

    if not isinstance(__cached_dict__[key1],dict) :
        __cached_dict__.update({key1:{}})
    return hash
def assign_expr(m,expr1) :
    global __cached_assign
    var1=expr1
    if m!=None and isinstance(m,list):
        m.append(var1)
    __cached_assign=var1
    return var1
def get_last_assign():
    return __cached_assign

### for test purpose only , really subroutine will be called from
#__init_settings()
#print(gsets['cwd'] + " " + gsets['template_dir'])
#__print_gsets()
