#!/usr/local/bin/perl -w
#------------------------------------------------------------------------------
# Licensed Materials - Property of IBM (C) Copyright IBM Corp. 2010, 2010
# All Rights Reserved US Government Users Restricted Rights - Use, duplication
# or disclosure restricted by GSA ADP Schedule Contract with IBM Corp
#------------------------------------------------------------------------------

#  perl sitaudit.pl
#
#  Identify situation characteristics
#     1) TEMS or Agent filtering
#
#  john alvord, IBM Corporation, 19 March 2014
#  jalvord@us.ibm.com
#
# tested on Windows Activestate 5.16.2
# Should work on Linux/Unix but not yet tested
#
# $DB::single=2;   # remember debug breakpoint

## todos
#
# Detect sampled sits with *UNTIL/*TTL less than Sampled interval
# warn on cases of Workflow policies correlated by hostname
# Does MS_Offline with *UNTIL/*TTL or *SIT cause excess workload

## 2008 APAR
## IZ02749: A situation is invalid if all of the following are true:

## The situations has:

## a reflex (take action)
## attributes from more than one attribute group
## both an *and and an *or condition.

#use warnings::unused; # debug used to check for unused variables
use strict;
use warnings;

# See short history at end of module

my $gVersion = "1.45000";
my $gWin = (-e "C://") ? 1 : 0;    # 1=Windows, 0=Linux/Unix

# communicate without certificates
BEGIN {
   $ENV{'PERL_NET_HTTPS_SSL_SOCKET_CLASS'} = "Net::SSL";
   $ENV{'PERL_LWP_SSL_VERIFY_HOSTNAME'} = 0;
};   #




use XML::TreePP;                # parse XML
use Marpa::R2;                  # Modern parse package
use Data::Dumper;               # debug only

# following object used to parse SOAP results and xml files.
my $tpp = XML::TreePP->new;

# a collection of variables which are used throughout the program.
# defined globally

my $args_start = join(" ",@ARGV);      # capture arguments for later processing
my $soap_rc;                           # return code from DoSoap call
my $soap_faultstr;                     # fault string from SOAP results
my $soap_faultcode;                    # fault code - where the fault originates
my $run_status = 0;                    # A count of pending runtime errors - used to allow multiple error detection before stopping process
my $oHub;                              # SOAP::Lite object to define connection

# some common variables

my @list = ();                         # used to get result of good SOAP capture
my $rc;
my $node;
my $myargs;
my $survey_sqls = 0;                     # count of SQLs
my $survey_sql_time = 0;                 # record total elapsed time in SQL processing
my @words = ();
my $rt;
my $debugfile;
my $ll;
my $pcount;
my $oneline;
my $sx;
my @connections = ();                    # list of possible hub TEMS servers
my $connection="";                       # connection chosen to primary hub TEMS
my $key;
my $f;

my $xmli = -1;
my @xmlfile = ();

# forward declarations of subroutines

sub init;                                # read command line and ini file
sub logit;                               # queue one record to survey log
sub DoSoap;                              # perform a SOAP request and return results
sub get_timestamp;                       # get current timestatmp
sub calc_timestamp;                      # Add or subtract time from an ITM timestamp
sub datadumperlog;                       # dump a variable using Dump::Data if installed
sub get_connection;                      # get current connection string
sub gettime;                             # get time
sub get_list;                            # unwind recursive array
sub init_soap;                           # input from Perl/SOAP to hub TEMS
sub init_all;                            # input from txt files
sub init_bulk;                           # input from bulkexportsot files
sub newsit;                              # create new situation entry
sub sitgroup_get_sits;                   # recursive sitgroup exploration
sub cycle_sit;                           # Cycled *SIT exploration
sub cycle_visit_sit;                     # recursive Cycled *SIT exploration - node visit

my $sitaudit_start_time = gettime();     # formated current time for report

my %configx;
$configx{"lst"} = [];
$configx{"txt"} = [];
$configx{"bulk"} = [];
$configx{"soap"} = [];

# Situation Group related data
my $gx;
my $grpi = -1;
my @grp = ();
my %grpx = ();
my @grp_sit = ();
my @grp_grp = ();
my %sum_sits = ();
my @sitcycle;
my %sitcyclex;
my $sitcyclerc;
my $sittopi;

my %pdtx;
my %pdtax;

my %nodel;

my %nsav;
my %nsav_aff;

my $nsav_online = 0;                      # count online and offline managed systems
my $nsav_offline = 0;

# Situation related data

my $siti = -1;                             # count of situations
my $curi;                                  # global index for subroutines
my @sit = ();                              # array of situations
my @sit_pdt = ();                          # array of predicates or situation formula
my @sit_fullname = ();                     # array of fullname
my @sit_psit = ();                         # array of printable situaton names
my @sit_sitinfo = ();                      # array of SITINFO columns
my @sit_autostart = ();                    # array of AUTOSTART columns
my %sitx = ();                             # Index from situation name to index
my @sit_value = ();                        # count of *VALUE
my @sit_sit = ();                          # count of *SIT
my @sit_sits = {};                         # hash of *SIT Sitnames
my @sit_str = ();                          # count of *STR
my @sit_scan = ();                         # count of *SCAN
my @sit_scan_ne = ();                      # count of *SCAN with invalid *NE
my @sit_change = ();                       # count of *CHANGE
my @sit_in = ();                           # count of *IN
my @sit_inct = ();                         # count of *IN entries
my @sit_pctchange = ();                    # count of *PCTCHANGE
my @sit_count = ();                        # count of *COUNT
my @sit_count_zero = ();                   # count of *COUNT w/value zero
my @sit_count_ltone = ();                  # count of *COUNT *LT/*LE 1
my @sit_count_lt = ();                     # count of *COUNT *LT/*LE more then 1
my @sit_count_process = ();                # count of *COUNT xxx.Process
my @sit_count_attr = ();                   # *COUNT attribute hash
my @sit_min = ();                          # count of *MIN
my @sit_max = ();                          # count of *MAX
my @sit_avg = ();                          # count of *AVG
my @sit_sum = ();                          # count of *SUM
my @sit_time = ();                         # count of *TIME
my @sit_time_same = ();                    # count of *TIME with same attribute table [bad]
my @sit_and = ();                          # count of *ANDs
my @sit_or = ();                           # count of *ORs
my @sit_noprivate = ();                    # Count of column functions not eligible for Private Situations
my @sit_noprivate_FP4 = ();                # Count of column functions not eligible for Private Situations ITM 630 FP4
my @sit_noprivate_V8 = ();                 # Count of column functions not eligible for Private Situations V8
my @sit_workprivate = ();                  # Count of column functions eligible for Private Situations with some work
my @sit_workprivate_FP4 = ();              # Count of column functions eligible for Private Situations with some work ITM 630 FP4
my @sit_workprivate_V8 = ();               # Count of column functions eligible for Private Situations with some work V8
my @sit_function = ();                     # Data about functions used
my @sit_until_ttl = ();                    # value of UNTIL/*TTL
my @sit_until_sit = ();                    # value of UNTIL/*SIT
my @sit_tables = ();                       # list of attribute groups
my @sit_tables_ct = ();                    # count of attribute groups
my @sit_alltables = ();                    # list of all attribute groups
my @sit_missing = ();                      # count of *MISSING
my @sit_missing_ct = ();                   # count of *MISSING comparands
my @sit_ms_offline = ();                   # count of MS_Offline type tests
my @sit_ms_online = ();                    # count of MS_Online type tests
my @sit_reason_ne_fa = ();                 # count of reason ne FA cases
my @sit_syntax = ();                       # syntax error caught
my @sit_persist = ();                      # persist count
my @sit_dst = ();                          # Event Destination(s)
my @sit_cmd = ();                          # 1 if CMD is present
my @sit_cmdtext = ();                      # cmd text
my @sit_autosopt = ();                     # autosopt column
my @sit_atom = ();                         # non-blank if DisplayItem
my @sit_multi = ();                        # 1 when multi-row formula
my @sit_ProcessFilter = ();                # 1 if process Filter present
my @sit_alwaystrue = ();                   # 1 if always true *value test
my @sit_reeval = ();                       # sampling interval in seconds
my @sit_reeval_bad_days = ();              # Problem when 1
my @sit_reeval_bad_time = ();              # Problem when 1
my @sit_filter = ();                       # Where filtered
my @sit_dist = ();                         # When 1, distributed
my @sit_dist_objaccl = ();                 # Situation Distributions in TOBJACCL and TGROUP/TGROUPI
my @sit_process = ();                      # Process type attribute group
my @sit_utfwild = ();                      # Unicode attribute with wildcard test
my @sit_fileinfo = ();                     # File Information type attribute group
my @sit_fileinfo_path = ();                # File Information type attribute group with Path
my @sit_fileinfo_file = ();                # File Information type attribute group with File
my @sit_nteventlog_logname = ();                # File Information type attribute group with File
my @sit_nteventlog_eventid = ();                # File Information type attribute group with File
my @sit_history_collect  = ();             # If History collection file, where collected - IRA or CMS
my @sit_history_interval = ();             # If History collection file, how often collected in seconds
my @sit_history_export   = ();             # If History collection file, how many collections before export
my $sit_distribution = 0;                  # when 1, distributions are present
my @sit_subset = ();                       # array of situations whose name is a subset of this one
my @sit_lstdate = ();                      # situation last changed timestamp
my @sit_aff_agent = ();                      # situation last changed timestamp
my @sit_atrlen = ();                       # Attribute incorrect length test
my @sit_attribs;                           # hash of used attributes
my @sit_domain_pass;                       # when 0, nothing in domain passes
my @sit_correlated;                        # count of correlated tests
my @sit_timeneeq;                          # *TIME test with *NE or *EQ
my @sit_timefuture;                        # *TIME with future test

my $sit_correlated_ct = 0;                 # number of correlated situations
my $sit_correlated_hr = 0;                 # number of ISITSTSH scans per hour for correlated situations

my $sit_tems_alert = 0;
my $sit_tems_alert_run = 0;
my $sit_tems_alert_dist = 0;

my %impossible;

# Check on a common error, using single digits for a time attribute

my %atrlenh = (
                 'Local_Time.Time' => 6,
                 'Local_Time.Minutes' => 2,
                 'Local_Time.Hours' => 2,
                 'Local_Time.Seconds' => 2,
                 'Local_Time.DayOfWeek' => 2,
                 'Universal_Time.Time' => 6,
                 'Universal_Time.Minutes' => 2,
                 'Universal_Time.Hours' => 2,
                 'Universal_Time.Seconds' => 2,
                 'Universal_Time.DayOfWeek' => 2,
              );

# Following is used to test certain formulae for no passing domain values
# "S" means string time followed by lower and upper numberic range
# potential future is "N" for numeric and "T" for specific values

my %domainx = (
                 'Local_Time.Hours' => ["S",0,23],
              );


# OS Agents multi-row attribute groups based on ITM 6.3 TEPS ODI files
# if attribute exists in a formula, it is a multi-row condition
# and a ATOM= should be present in SITINFO
# This table is calculated from product provided attribute files. The table
# is extended to other tables dynamically when a sampled situation is observed
# with an ATOM in a situation.

my %multih = (
              'System' => 'S', # 'UX'
              'SP2System' => 'S', # 'UX'
              'Unix_Memory' => 'S', # 'UX'
              'Unix_File_Pattern' => 'S', # 'UX'
              'Unix_File_Comparison' => 'S', # 'UX'
              'Machine_Information' => 'S', # 'UX'
              'UNIX_TCP_Statistics' => 'S', # 'UX'
              'AIX_LPAR' => 'S', # 'UX'
              'AIX_System_IO' => 'S', # 'UX'
              'Disk' => 'M', # 'UX'
              'Disk_Performance' => 'M', # 'UX'
              'Network' => 'M', # 'UX'
              'User' => 'M', # 'UX'
              'Process' => 'M', # 'UX'
              'File_Information' => 'M', # 'UX'
              'N_F_S_and_R_P_C_Statistics' => 'M', # 'UX'
              'SMP_CPU' => 'M', # 'UX'
              'Unix_Print_Queue' => 'M', # 'UX'
              'Unix_Group' => 'M', # 'UX'
              'Unix_Ping' => 'M', # 'UX'
              'Unix_All_Users' => 'M', # 'UX'
              'Solaris_Zones' => 'M', # 'UX'
              'UNIX_IP_Address' => 'M', # 'UX'
              'KCA_UX_Configuration_Information' => 'M', # 'UX'
              'KCA_UX_Agent_Availability_Management_Status' => 'M', # 'UX'
              'KCA_UX_Agent_Active_Runtime_Status' => 'M', # 'UX'
              'AIX_AMS' => 'M', # 'UX'
              'AIX_DEVICES' => 'M', # 'UX'
              'AIX_WPAR_Information' => 'M', # 'UX'
              'AIX_WPAR_CPU' => 'M', # 'UX'
              'AIX_WPAR_Physical_Memory' => 'M', # 'UX'
              'AIX_WPAR_Network' => 'M', # 'UX'
              'AIX_WPAR_FileSystem' => 'M', # 'UX'
              'AIX_Defined_Users' => 'M', # 'UX'
              'Data_Collection_Status' => 'M', # 'UX'
              'AIX_Physical_Volumes' => 'M', # 'UX'
              'AIX_Volume_Groups' => 'M', # 'UX'
              'AIX_Logical_Volumes' => 'M', # 'UX'
              'UNIX_DEVICES' => 'M', # 'UX'
              'Top_CPU_Processes' => 'M', # 'UX'
              'Top_Memory_Processes' => 'M', # 'UX'
              'KLZ_CPU_Averages' => 'S', # 'LZ'
              'KLZ_System_Statistics' => 'S', # 'LZ'
              'KLZ_Swap_Rate' => 'S', # 'LZ'
              'KLZ_VM_Stats' => 'S', # 'LZ'
              'KLZ_RPC_Statistics' => 'S', # 'LZ'
              'Linux_Machine_Information' => 'S', # 'LZ'
              'KLZ_TCP_Statistics' => 'S', # 'LZ'
              'KLZ_LPAR' => 'S', # 'LZ'
              'Linux_CPU_Averages' => 'S', # 'LZ'
              'Linux_System_Statistics' => 'S', # 'LZ'
              'Linux_Swap_Rate' => 'S', # 'LZ'
              'Linux_VM_Stats' => 'S', # 'LZ'
              'Linux_RPC_Statistics' => 'S', # 'LZ'
              'KLZ_User_Login' => 'M', # 'LZ'
              'KLZ_Disk' => 'M', # 'LZ'
              'KLZ_Disk_Usage_Trends' => 'M', # 'LZ'
              'KLZ_Network' => 'M', # 'LZ'
              'KLZ_CPU' => 'M', # 'LZ'
              'KLZ_Process' => 'M', # 'LZ'
              'KLZ_Process_User_Info' => 'M', # 'LZ'
              'KLZ_Sockets_Status' => 'M', # 'LZ'
              'KLZ_Sockets_Detail' => 'M', # 'LZ'
              'KLZ_Disk_IO' => 'M', # 'LZ'
              'KLZ_IO_Ext' => 'M', # 'LZ'
              'KLZ_NFS_Statistics' => 'M', # 'LZ'
              'Linux_CPU_Config' => 'M', # 'LZ'
              'Linux_OS_Config' => 'M', # 'LZ'
              'Linux_File_Information' => 'M', # 'LZ'
              'Linux_Host_Availability' => 'M', # 'LZ'
              'Linux_File_Pattern' => 'M', # 'LZ'
              'Linux_File_Comparison' => 'M', # 'LZ'
              'Linux_All_Users' => 'M', # 'LZ'
              'Linux_Group' => 'M', # 'LZ'
              'Linux_IP_Address' => 'M', # 'LZ'
              'Linux_User_Login' => 'M', # 'LZ'
              'Linux_Disk' => 'M', # 'LZ'
              'Linux_Disk_Usage_Trends' => 'M', # 'LZ'
              'Linux_Network' => 'M', # 'LZ'
              'Linux_CPU' => 'M', # 'LZ'
              'Linux_Process' => 'M', # 'LZ'
              'Linux_Process_User_Info' => 'M', # 'LZ'
              'Linux_Sockets_Status' => 'M', # 'LZ'
              'Linux_Sockets_Detail' => 'M', # 'LZ'
              'Linux_Disk_IO' => 'M', # 'LZ'
              'Linux_IO_Ext' => 'M', # 'LZ'
              'Linux_NFS_Statistics' => 'M', # 'LZ'
              'KCA_LZ_Configuration_Information' => 'M', # 'LZ'
              'KCA_LZ_Agent_Availability_Management_Status' => 'M', # 'LZ'
              'KCA_LZ_Agent_Active_Runtime_Status' => 'M', # 'LZ'
              'NT_System' => 'S', # 'NT'
              'NT_Memory_64' => 'S', # 'NT'
              'NT_Memory' => 'S', # 'NT'
              'NT_Objects' => 'S', # 'NT'
              'Active_Server_Pages' => 'S', # 'NT'
              'HTTP_Content_Index' => 'S', # 'NT'
              'HTTP_Service' => 'S', # 'NT'
              'FTP_Server_Statistics' => 'S', # 'NT'
              'IIS_Statistics' => 'S', # 'NT'
              'UDP_Statistics' => 'S', # 'NT'
              'TCP_Statistics' => 'S', # 'NT'
              'ICMP_Statistics' => 'S', # 'NT'
              'Gopher_Statistics' => 'S', # 'NT'
              'MSMQ_Information_Store' => 'S', # 'NT'
              'MSMQ_Service' => 'S', # 'NT'
              'RAS_Total' => 'S', # 'NT'
              'NT_Cache' => 'S', # 'NT'
              'DHCP_Server' => 'S', # 'NT'
              'DNS_Memory' => 'S', # 'NT'
              'DNS_Zone_Transfer' => 'S', # 'NT'
              'DNS_Dynamic_Update' => 'S', # 'NT'
              'DNS_Query' => 'S', # 'NT'
              'DNS_WINS' => 'S', # 'NT'
              'NT_Event_Log' => 'S', # 'NT'
              'NT_Server' => 'S', # 'NT'
              'NT_Redirector' => 'S', # 'NT'
              'NT_Processor_Summary' => 'S', # 'NT'
              'NT_BIOS_Information' => 'S', # 'NT'
              'NT_Computer_Information' => 'S', # 'NT'
              'VM_Memory' => 'S', # 'NT'
              'NT_Logical_Disk' => 'M', # 'NT'
              'NT_Physical_Disk' => 'M', # 'NT'
              'NT_Process_64' => 'M', # 'NT'
              'NT_Process' => 'M', # 'NT'
              'NT_Processor' => 'M', # 'NT'
              'NT_Paging_File' => 'M', # 'NT'
              'WTOBJECTS' => 'M', # 'NT'
              'NT_Monitored_Logs_Report' => 'M', # 'NT'
              'NT_FILE_TREND' => 'M', # 'NT'
              'NT_Network_Interface' => 'M', # 'NT'
              'Network_Interface' => 'M', # 'NT'
              'Network_Segment' => 'M', # 'NT'
              'MSMQ_Queue' => 'M', # 'NT'
              'MSMQ_Sessions' => 'M', # 'NT'
              'RAS_Port' => 'M', # 'NT'
              'NT_Printer' => 'M', # 'NT'
              'NT_Print_Job' => 'M', # 'NT'
              'NT_Services' => 'M', # 'NT'
              'NT_Service_Dependencies' => 'M', # 'NT'
              'NT_Devices' => 'M', # 'NT'
              'NT_Device_Dependencies' => 'M', # 'NT'
              'FTP_Service' => 'M', # 'NT'
              'Web_Service' => 'M', # 'NT'
              'Indexing_Service' => 'M', # 'NT'
              'Indexing_Service_Filter' => 'M', # 'NT'
              'NNTP_Commands' => 'M', # 'NT'
              'NNTP_Server' => 'M', # 'NT'
              'SMTP_Server' => 'M', # 'NT'
              'Job_Object' => 'M', # 'NT'
              'NT_Job_Object_Details' => 'M', # 'NT'
              'Job_Object_Details' => 'M', # 'NT'
              'Print_Queue' => 'M', # 'NT'
              'NT_Thread' => 'M', # 'NT'
              'NT_Server_Work_Queues_64' => 'M', # 'NT'
              'NT_Server_Work_Queues' => 'M', # 'NT'
              'NT_Registry' => 'M', # 'NT'
              'Process_IO' => 'M', # 'NT'
              'NT_Network_Port' => 'M', # 'NT'
              'NT_Processor_Information' => 'M', # 'NT'
              'NT_IP_Address' => 'M', # 'NT'
              'NT_Mount_Points' => 'M', # 'NT'
              'KCA_Configuration_Information' => 'M', # 'NT'
              'KCA_Agent_Availability_Management_Status' => 'M', # 'NT'
              'KCA_Agent_Active_Runtime_Status' => 'M', # 'NT'
              'VM_Processor' => 'M', # 'NT'
              'OS400_Network' => 'S', # 'A4'
              'OS400_System_Values_Acct' => 'S', # 'A4'
              'OS400_System_Values' => 'S', # 'A4'
              'OS400_System_Values_Device' => 'S', # 'A4'
              'OS400_System_Values_IPL' => 'S', # 'A4'
              'OS400_System_Values_Prob' => 'S', # 'A4'
              'OS400_System_Values_Perf' => 'S', # 'A4'
              'OS400_System_Values_User' => 'S', # 'A4'
              'OS400_System_Status' => 'S', # 'A4'
              'i5OS_System_Statistics' => 'S', # 'A4'
              'i5OS_Net_Server' => 'S', # 'A4'
              'i5OS_Miscellaneous' => 'S', # 'A4'
              'i5OS_System_Value_Sys_Ctl_1' => 'S', # 'A4'
              'i5OS_System_Value_Sys_Ctl_2' => 'S', # 'A4'
              'i5OS_System_Value_Allocation' => 'S', # 'A4'
              'i5OS_System_Value_Date_Time' => 'S', # 'A4'
              'i5OS_System_Value_Editing' => 'S', # 'A4'
              'i5OS_System_Value_Security' => 'S', # 'A4'
              'i5OS_System_Value_Other' => 'S', # 'A4'
              'OS400_Comm_Async' => 'M', # 'A4'
              'OS400_Comm_Bisync' => 'M', # 'A4'
              'OS400_Controller' => 'M', # 'A4'
              'OS400_DB_Member' => 'M', # 'A4'
              'OS400_Device' => 'M', # 'A4'
              'OS400_Disk_Unit' => 'M', # 'A4'
              'OS400_Comm_Ethernet' => 'M', # 'A4'
              'OS400_Job_Queue' => 'M', # 'A4'
              'OS400_Line' => 'M', # 'A4'
              'OS400_Object' => 'M', # 'A4'
              'OS400_I/O_Processor' => 'M', # 'A4'
              'OS400_Job' => 'M', # 'A4'
              'OS400_Storage_Pool' => 'M', # 'A4'
              'OS400_Subsystem' => 'M', # 'A4'
              'OS400_Comm_SDLC' => 'M', # 'A4'
              'OS400_Comm_Token_Ring' => 'M', # 'A4'
              'OS400_Comm_X25' => 'M', # 'A4'
              'i5OS_Auxiliary_Storage_Pool' => 'M', # 'A4'
              'i5OS_TCPIP_Logical_Interface' => 'M', # 'A4'
              'i5OS_TCPIP_Service' => 'M', # 'A4'
              'i5OS_Network_Interface' => 'M', # 'A4'
              'i5OS_Network_Server' => 'M', # 'A4'
              'i5OS_Disk' => 'M', # 'A4'
              'i5OS_Output_Queue' => 'M', # 'A4'
              'i5OS_History_Log' => 'M', # 'A4'
              'i5OS_Integrated_File_System_Object' => 'M', # 'A4'
              'i5OS_Job_Log' => 'M', # 'A4'
              'i5OS_Distribution_Queue' => 'M', # 'A4'
              'i5OS_Inactive_Job' => 'M', # 'A4'
              'i5OS_User_and_Group' => 'M', # 'A4'
              'i5OS_TCPIP_Route' => 'M', # 'A4'
              'i5OS_TCPIP_Host' => 'M', # 'A4'
              'i5OS_Cluster_Node' => 'M', # 'A4'
              'i5OS_Cluster_Resource_Group' => 'M', # 'A4'
              'i5OS_Cluster_Monitored_Resources' => 'M', # 'A4'
              'i5OS_Licensed_Program_Product' => 'M', # 'A4'
              'i5OS_Program_Temporary_Fix' => 'M', # 'A4'
              'i5OS_Group_Program_Temporary_Fix' => 'M', # 'A4'
              'i5OS_Group_PTF_Details' => 'M', # 'A4'
              'i5OS_IOA_Cache_Battery' => 'M', # 'A4'
              'KR2_THREAD_POOL_STATUS' => 'S', # R2
              'KR2_VIRTUAL_MEMORY' => 'S', # R2
              'KR2_SYSTEM' => 'S', # R2
              'KR2_TERMINAL_SERVICES' => 'S', # R2
              'KR2_HRSYSTEM' => 'S', # R2
              'KR2_PROCESSOR_UTILIZATION_TOTAL' => 'S', # R2
              'KR2_COMPUTER_SYSTEM' => 'M', # R2
              'KR2_DISK' => 'M', # R2
              'KR2_HRDEVICETABLE' => 'M', # R2
              'KR2_HRPROCESSOR' => 'M', # R2
              'KR2_HRPROCESSORTABLE' => 'M', # R2
              'KR2_HRSTORAGETABLE' => 'M', # R2
              'KR2_LOGICAL_DISK' => 'M', # R2
              'KR2_MANAGED_SYSTEMS_SNMP' => 'M', # R2
              'KR2_MANAGED_SYSTEMS_WMI' => 'M', # R2
              'KR2_MEMORY' => 'M', # R2
              'KR2_NETWORK' => 'M', # R2
              'KR2_NETWORK_INTERFACES' => 'M', # R2
              'KR2_OPERATING_SYSTEM' => 'M', # R2
              'KR2_PAGE_FILE_USAGE_DETAILS' => 'M', # R2
              'KR2_PAGING_FILE_SUMMARY' => 'M', # R2
              'KR2_PERFORMANCE_OBJECT_STATUS' => 'M', # R2
              'KR2_PHYSICAL_DISK' => 'M', # R2
              'KR2_PHYSICAL_MEMORY' => 'M', # R2
              'KR2_PROCESS' => 'M', # R2
              'KR2_PROCESSES' => 'M', # R2
              'KR2_PROCESSOR' => 'M', # R2
              'KR2_PROCESSOR_DETAILS' => 'M', # R2
              'KR2_TERMINAL_SERVICES_SESSION' => 'M', # R2
              'KR2_TERMINAL_SERVICES_SESSION_MEMORY' => 'M', # R2
              'KR2_USER_ACCOUNTS' => 'M', # R2
              'KR2_WIN_PERFORMANCE_OBJECT_STATUS' => 'M', # R2
              'KR2_WINDOWS_SERVICES' => 'M', # R2
              'KR2_WMI_PERFORMANCE_OBJECT_STATUS' => 'M', # R2
              'KR3_THREAD_POOL_STATUS' => 'S', # R3
              'KR3_TOTAL_VIRTUAL_MB' => 'S', # R3
              'KR3_USED_VIRTUAL_MB' => 'S', # R3
              'KR3_VIRTUAL_MEMORY' => 'S', # R3
              'KR3_PROCESSOR_UTILIZATION_TOTAL' => 'S', # R3
              'KR3_SYSTEM' => 'S', # R3
              'KR3_AIX_PERFORMANCE_OBJECT_STATUS' => 'M', # R3
              'KR3_AIXLOGICALVOLUMETABLE' => 'M', # R3
              'KR3_AIXLOGINUSERTABLE' => 'M', # R3
              'KR3_AIXPAGETABLE' => 'M', # R3
              'KR3_AIXPHYSICALVOLUMETABLE' => 'M', # R3
              'KR3_AIXUSRTABLE' => 'M', # R3
              'KR3_AIXVOLUMEGROUPTABLE' => 'M', # R3
              'KR3_DISK' => 'M', # R3
              'KR3_HRDEVICETABLE' => 'M', # R3
              'KR3_HRPROCESSOR' => 'M', # R3
              'KR3_HRPROCESSORTABLE' => 'M', # R3
              'KR3_HRSTORAGETABLE' => 'M', # R3
              'KR3_MANAGED_SYSTEMS' => 'M', # R3
              'KR3_MEMORY' => 'M', # R3
              'KR3_NETWORK' => 'M', # R3
              'KR3_PERFORMANCE_OBJECT_STATUS' => 'M', # R3
              'KR3_PROCESSES' => 'M', # R3
              'KR4_THREAD_POOL_STATUS' => 'S', # R4
              'KR4_PROCESSOR' => 'S', # R4
              'KR4_SYSTEM' => 'S', # R4
              'KR4_UCDMEMORY' => 'S', # R4
              'KR4_TOTAL_VIRTUAL_MB' => 'S', # R4
              'KR4_USED_VIRTUAL_MB' => 'S', # R4
              'KR4_VIRTUAL_MEMORY' => 'S', # R4
              'KR4_DISK' => 'M', # R4
              'KR4_HRSTORAGETABLE' => 'M', # R4
              'KR4_LNX_PERFORMANCE_OBJECT_STATUS' => 'M', # R4
              'KR4_MANAGED_SYSTEMS' => 'M', # R4
              'KR4_MEMORY' => 'M', # R4
              'KR4_MEMORY_UCD_HRSTORAGE' => 'M', # R4
              'KR4_NETWORK' => 'M', # R4
              'KR4_PERFORMANCE_OBJECT_STATUS' => 'M', # R4
              'KR4_PROCESSES' => 'M', # R4
              'KR5_THREAD_POOL_STATUS' => 'S', # R5
              'KR5_MEMORY' => 'S', # R5
              'KR5_PROCESSOR' => 'S', # R5
              'KR5_SYSTEM' => 'S', # R5
              'KR5_DISK' => 'M', # R5
              'KR5_HP_PERFORMANCE_OBJECT_STATUS' => 'M', # R5
              'KR5_MANAGED_SYSTEMS' => 'M', # R5
              'KR5_NETWORK' => 'M', # R5
              'KR5_PERFORMANCE_OBJECT_STATUS' => 'M', # R5
              'KR5_PROCESSES' => 'M', # R5
              'KR6_THREAD_POOL_STATUS' => 'S', # R6
              'KR6_MEMORY' => 'S', # R6
              'KR6_PROCESSOR' => 'S', # R6
              'KR6_SYSTEM' => 'S', # R6
              'KR6_SMC_MEMORY' => 'S', # R6
              'KR6_SMC_PROCESSOR_SUMMARY' => 'S', # R6
              'KR6_SMC_SYSTEM_INFORMATION' => 'S', # R6
              'KR6_HRSYSTEM' => 'S', # R6
              'KR6_SMA_MEMORY' => 'S', # R6
              'KR6_SMA_PROCESSOR' => 'S', # R6
              'KR6_CIM_PERFORMANCE_OBJECT_STATUS' => 'M', # R6
              'KR6_DISK' => 'M', # R6
              'KR6_HRSTORAGETABLE' => 'M', # R6
              'KR6_MANAGED_CIM_SYSTEMS' => 'M', # R6
              'KR6_MANAGED_SMA_SYSTEMS' => 'M', # R6
              'KR6_MANAGED_SMC_SYSTEMS' => 'M', # R6
              'KR6_NETWORK' => 'M', # R6
              'KR6_PERFORMANCE_OBJECT_STATUS' => 'M', # R6
              'KR6_PROCESS' => 'M', # R6
              'KR6_PROCESSES' => 'M', # R6
              'KR6_SMA_DISK' => 'M', # R6
              'KR6_SMA_NETWORK' => 'M', # R6
              'KR6_SMA_PERFORMANCE_OBJECT_STATUS' => 'M', # R6
              'KR6_SMC_NETWORK' => 'M', # R6
              'KR6_SMC_NFS' => 'M', # R6
              'KR6_SMC_PERFORMANCE_OBJECT_STATUS' => 'M', # R6
              'KR6_SMC_PROCESS' => 'M', # R6
              'KR6_SMC_PROCLISTSH' => 'M', # R6
              'KR6_SMC_UFS' => 'M', # R6
              'KR6_SMC_VXFS' => 'M', # R6
              'KHD_DB_INFO' => 'S', # HD
              'KHD_CONFIG' => 'S', # HD
              'KHD_RPCSOURCE_STATISTICS' => 'S', # HD
              'KHD_WORK_QUEUE' => 'S', # HD
              'KHD_LOAD_STATISTICS' => 'S', # HD
              'KHD_NODE_LIST' => 'M', # HD
              'KHD_REGISTRATION_ADDRESS_LIST' => 'M', # HD
              'KHD_WAREHOUSE_TEMS_LIST' => 'M', # HD
              'KSY_SUMMARIZATION_STATISTICS' => 'S', # SY
              'KSY_SUMMARIZATION_CONFIG' => 'S', # SY
              'KSY_CONNECTIVITY' => 'S', # SY
              'KSY_TABLE_STATISTICS' => 'M', # SY
              'KSY_NODE_FAILURES' => 'M', # SY
              'KPA_T_MOSWOS_AGENT' => 'S', # PA
              'KPA_T_MOSWOS_DB' => 'S', # PA
              'KPA_T_MOSWOS_SUB_AGENT' => 'S', # PA
              'KPA_T_MOSWOS_TASK' => 'S', # PA
              'KPA_GENERIC_D32_NLT_FCAST' => 'M', # PA
              'KPA_GENERIC_D32_NLT_STATUS' => 'M', # PA
              'KPA_GENERIC_D64_NLT_FCAST' => 'M', # PA
              'KPA_GENERIC_D64_NLT_STATUS' => 'M', # PA
              'KPA_GENERIC_I32_NLT_FCAST' => 'M', # PA
              'KPA_GENERIC_I32_NLT_STATUS' => 'M', # PA
              'KPA_GENERIC_I64_NLT_FCAST' => 'M', # PA
              'KPA_GENERIC_I64_NLT_STATUS' => 'M', # PA
              'KDY_Configuration_parms' => 'M', # DY
              'KDY_Execution_parms' => 'M', # DY
              'KDY_Inventory_Table' => 'M', # DY
              'KDY_Request' => 'M', # DY
             );

my %hevmap = ();

my %hactp = ();

my %hovrd = ();

# following us a hash list of non-private situation rules

my %hprivate_reasons = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

my %hprivate_work = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

my %hprivate_reasons_FP4 = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

my %hprivate_work_FP4 = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

my %hprivate_reasons_V8 = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

my %hprivate_work_V8 = (
   '*COUNT'        => 0,
   '*TIME'        => 0,
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   'UADVISOR'      => 0,
   'SyntaxError'   => 0,
   'MS_OFFLINE'    => 0,
   'MultiTable'    => 0,
   'MultiCOUNT'    => 0,
   'Persist'       => 0,
   'ActionCommandTEMS' => 0,
   'AND+OR'        => 0,
   'AND>9'         => 0,
   'OR>10'         => 0,
   '*HISTRULE'     => 0,
   '*IN'           => 0,
   'InvalidTime'   => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   'DisplayItem'    => 0,
   'EventDest!=0'    => 0,
   'EventMap'    => 0,
   'Policy'    => 0,
   'Override'    => 0,
   'Longname'    => 0,
   'IntervalDays'    => 0,
);

# following us a hash list of all functions

my %hfunction = (
   '*AVG'          => 0,
   '*SUM'          => 0,
   '*CHANGE'       => 0,
   '*PCTCHANGE'    => 0,
   '*MIN'          => 0,
   '*MAX'          => 0,
   '*VALUE'        => 0,
   '*AND'         => 0,
   '*SCAN'         => 0,
   '*STR'          => 0,
   '*SIT'          => 0,
   '*UNTIL*SIT'   => 0,
   '*UNTIL*TTL*SIT'    => 0,
   '*UNTIL*TTL'     => 0,
   '*MISSING'     => 0,
   '*COUNT'     => 0,
   '*TIME'     => 0,
);

# following situations exhibit SP2OS-ish behavior. This is a very early style where
# a UADVISOR situation is used to keep an in storage hub virtual table up to date. This fails
# badly when there are many [40+] agents and causes TEMS communication outages. They are
# identified here to alert the user.

my %hSP2OS = (
UADVISOR_OMUNX_SP2OS => 1,
UADVISOR_KOQ_VKOQDBMIR => 1,
UADVISOR_KOQ_VKOQLSDBD => 1,
UADVISOR_KOQ_VKOQSRVR => 1,
UADVISOR_KOQ_VKOQSRVRE => 1,
UADVISOR_KOR_VKORSRVRE => 1,
UADVISOR_KOR_VKORSTATE => 1,
UADVISOR_KOY_VKOYSRVR => 1,
UADVISOR_KOY_VKOYSRVRE => 1,
UADVISOR_KQ5_VKQ5CLUSUM => 1,
);

# Process type historical data which is expensive and not very useful

my %hProcess = (
UADVISOR_KNT_NTPROCESS => 1,
UADVISOR_OMUNX_UNIXPS => 1,
UADVISOR_KLZ_KLZPROC => 1,
);

# built in attribute substituations in some case

my %hBuiltIn = (
   _SITNAME => 1,
   _SITTIME => 1,
   _SITNODE => 1,
   _PREDICATE => 1,
);

my %Atrg = ();                            # track Attribute table usage looking for mixed pure and sampled mixtures

my %hSkip = ();

# option and ini file variables variables

my $opt_txt;                    # input from .txt files
my $opt_txt_tsitdesc;           # TSITDESC txt file
my $opt_txt_tname;              # TNAME txt file
my $opt_txt_tobjaccl;           # TOBJACCL txt file
my $opt_txt_tgroup;             # TGROUP txt file
my $opt_txt_tgroupi;            # TGROUPI txt file
my $opt_txt_evntmap;            # EVNTMAP txt file
my $opt_txt_tactypcy;           # TACTYPCY txt file
my $opt_txt_toverride;          # TOVERRIDE txt file
my $opt_txt_tnodelst;           # TNODELST txt file
my $opt_txt_tnodesav;           # TNODELST txt file
my $opt_lst;                    # input from .lst files
my $opt_lst_tsitdesc;           # TSITDESC lst file
my $opt_lst_tsitdesc1;          # TSITDESC_1 lst file
my $opt_lst_tname;              # TNAME lst file
my $opt_lst_tobjaccl;           # TOBJACCL lst file
my $opt_lst_tgroup;             # TGROUP lst file
my $opt_lst_tgroupi;            # TGROUPI lst file
my $opt_lst_evntmap;            # EVNTMAP lst file
my $opt_lst_tactypcy;           # TACTYPCY lst file
my $opt_lst_toverride;          # TOVERRIDE lst file
my $opt_lst_tnodelst;           # TNODELST lst file
my $opt_lst_tnodesav;           # TNODELST lst file
my $opt_bulk;                   # input from bulkexportsit files
my $opt_bulk_path;              # input from bulkexportsit files
my $opt_soap;                   # input from hub TEMS via SOAP
my $opt_log;                    # name of log file
my $opt_ini;                    # name of ini file
my $opt_noauto;                    # create editsit autostart=off for impossible cases
my $opt_debuglevel;             # Debug level
my $opt_debug;                  # Debug level
my $opt_h;                      # help file
my $opt_v;                      # verbose flag
my $opt_vt;                     # verbose traffic flag
my $opt_dpr;                    # dump data structure flag
my $opt_std;                    # Credentials from standard input
my $opt_soap_timeout;           # How long to wait SOAP request
my $opt_o;                      # output file
my $opt_workpath;               # Directory to store output files
my $opt_runall;                 # check Run at Startup = *OFF situations
my $opt_pdtmsl;                 # generate MSLs for duplicate PDTs
my $opt_sitpdt;
my $opt_pdtlim;                 # low limit on reporting duplicate PDTs
my $user="";
my $passwd="";
my $opt_nodist;                 # report on AUTOSTART=*YES but no distribution
my $opt_nohdr = 0;              # skip header to make regression testing easier
my $opt_dist;                   # report on distribution
my $opt_sth24;                  # warn when data collection not 24 hours
my $opt_agent_filter;           # report on Agent Filtering
my $opt_syntax;                 # syntax tracing
my $opt_private;                # private situation audit
my $opt_function;               # list of function usage
my $opt_a;                      # export situation attribute group
my $opt_nofull;
my $opt_all = 0;

my %advtextx = ();
my $advkey = "";
my $advtext = "";
my $advline;
my %advgotx = ();
my %advrptx = ();


while (<main::DATA>)
{
  $advline = $_;
  $advline =~ s/\x0d//g if $gWin == 0;
  if ($advkey eq "") {
     chomp $advline;
     $advkey = $advline;
     next;
  }
  if (length($advline) >= 13) {
     if ((substr($advline,0,8) eq "SITAUDIT") or (substr($advline,0,9) eq "SITREPORT")){
        $advtextx{$advkey} = $advtext;
        chomp $advline;
        $advkey = $advline;
        $advtext = "";
        next;
     }
  }
  $advtext .= $advline;
}
$advtextx{$advkey} = $advtext;

# do basic initialization from parameters, ini file and standard input

$rc = init($args_start);

$opt_log = $opt_workpath . $opt_log;
open FH, ">>$opt_log" or die "can't open $opt_log: $!";

logit(0,"SITAUDIT000I - ITM_Situation_Audit $gVersion $args_start");

my $advi = -1;
my @advonline = ();
my @advsit = ();
my @advimpact = ();
my @advcode = ();
my %advx = ();
my $rptkey = "";

my %advcx = (
               "SITAUDIT0999E" => "100",
               "SITAUDIT1000E" => "100",
               "SITAUDIT1001E" => "90",
               "SITAUDIT1002E" => "90",
               "SITAUDIT1003E" => "90",
               "SITAUDIT1004E" => "90",
               "SITAUDIT1005E" => "90",
               "SITAUDIT1006E" => "100",
               "SITAUDIT1007E" => "75",
               "SITAUDIT1008E" => "90",
               "SITAUDIT1009E" => "75",
               "SITAUDIT1010W" => "75",
               "SITAUDIT1011E" => "100",
               "SITAUDIT1012E" => "100",
               "SITAUDIT1013W" => "95",
               "SITAUDIT1014E" => "75",
               "SITAUDIT1015W" => "50",
               "SITAUDIT1016W" => "75",
               "SITAUDIT1017W" => "50",
               "SITAUDIT1018W" => "75",
               "SITAUDIT1019I" => "10",
               "SITAUDIT1020W" => "50",
               "SITAUDIT1021W" => "90",
               "SITAUDIT1022W" => "100",
               "SITAUDIT1023W" => "25",
               "SITAUDIT1024E" => "90",
               "SITAUDIT1025W" => "95",
               "SITAUDIT1026W" => "95",
               "SITAUDIT1027W" => "75",
               "SITAUDIT1028E" => "100",
               "SITAUDIT1029W" => "90",
               "SITAUDIT1030W" => "60",
               "SITAUDIT1031I" => "20",
               "SITAUDIT1032I" => "5",
               "SITAUDIT1033W" => "75",
               "SITAUDIT1034W" => "100",
               "SITAUDIT1035W" => "10",
               "SITAUDIT1036W" => "75",
               "SITAUDIT1037I" => "10",
               "SITAUDIT1038W" => "65",
               "SITAUDIT1039W" => "65",
               "SITAUDIT1040E" => "75",
               "SITAUDIT1041W" => "60",
               "SITAUDIT1042W" => "25",
               "SITAUDIT1043W" => "25",
               "SITAUDIT1044W" => "75",
               "SITAUDIT1045W" => "50",
               "SITAUDIT1046E" => "100",
               "SITAUDIT1047E" => "90",
               "SITAUDIT1048E" => "90",
               "SITAUDIT1049E" => "100",
               "SITAUDIT1050E" => "50",
               "SITAUDIT1051E" => "90",
               "SITAUDIT1052E" => "100",
               "SITAUDIT1053E" => "100",
               "SITAUDIT1054E" => "90",
               "SITAUDIT1055W" => "75",
               "SITAUDIT1056W" => "90",
               "SITAUDIT1057W" => "90",
               "SITAUDIT1058E" => "100",
               "SITAUDIT1059W" => "90",
               "SITAUDIT1060W" => "50",
               "SITAUDIT1061E" => "90",
               "SITAUDIT1062W" => "95",
               "SITAUDIT1063E" => "100",
            );


# process three different sources of situation data

if ($opt_soap == 1) {                   # SOAP
   $rc = init_soap();
} elsif ($opt_txt == 1) {               # txt files
   $rc = init_all();
} elsif ($opt_lst == 1) {               # lst files
   $rc = init_all();
} else {
   $rc = init_bulk();                   # bulkexportsit files

}


# Following is an informal BNF description of the Situation Formula mini-language
# It is *not* used in the ITM product directly, but a version was used many years ago.
# This has been adapated to recent ITM changes and also for MARPA requirements.

my $dsl = <<'END_OF_DSL';

:start ::= formula

:default ::= action => ::array

lexeme default = latm => 1

:discard ~ ws

formula               ::= '*IF' <condition_list>
                      |   '*IF' <condition_list> <until_clause>

<condition_list>      ::=  <condition>
                      |    '(' <condition_list> ')'
                      |    <condition_list> <logical_operator> <condition_list>  action => do_condition

<logical_operator>    ::= '*AND' | '*OR'

<condition>           ::= <value_condition>
                      |   <count_condition>
                      |   <value_condition_in>
                      |   <scalar_condition>
                      |   <time_condition>
                      |   <missing_condition>
                      |   <str_func_condition>
                      |   <situation_condition>
                      |   <histrule_condition>

<value_condition>     ::= '*VALUE' <attribute> <comparison> <literal>   action => do_value

<count_condition>     ::= '*COUNT' <attribute> <comparison> <literal>   action => do_count


<comparison>          ::= '*EQ' | '*GE' | '*GT' | '*LE' | '*LT' | '*NE'

<value_condition_in>  ::= '*VALUE' <attribute> '*IN' '(' <comma_separated_list> ')'   action => do_value_in

<literal>             ::= <quoted_string> | <null_string> | <number> | enum | <literal_word>

<attribute>           ::= id'.' id
                      | id


<scalar_condition>    ::= <scalar_function> <attribute> <comparison> <number>   action => do_scalar
                      |   <minmax_function> <attribute> '*EQ' '*TRUE'   action => do_minmax

<scalar_function>     ::= '*AVG' | '*SUM' | '*CHANGE' | '*PCTCHANGE'

<time_condition>      ::= '*TIME' <attribute> <comparison> <quoted_string>      action => do_time

<minmax_function>     ::= '*MIN' | '*MAX'

<missing_condition>   ::= '*MISSING' <attribute> '*EQ' '(' <comma_separated_list> ')'  action => do_missing

<comma_separated_list> ::= <quoted_string>
                      |   <literal_word>
                      |   <quoted_string> ',' <comma_separated_list>

<str_func_condition>  ::= '*SCAN' <attribute> <comparison> <literal_word>         action => do_scan
                      |   '*SCAN' <attribute> <comparison> <quoted_string>   action => do_scan
                      |   '*STR' <attribute> <comparison> <strdigit> ',' <literal_word>       action => do_str
                      |   '*STR' <attribute> <comparison> <strdigit> ',' <quoted_string> action => do_str
                      |   '*STR' <attribute> <comparison> <quoted_string> action => do_str

<strdigit>            ~ <digits>

<situation_condition> ::= '*SIT' <situation> '*EQ' '*TRUE'                         action => do_sit

<histrule_condition>  ::= '*HISTRULE' <hist_sql>                   action => do_histrule_where

<situation>           ::= <idsit>

<until_clause>        ::= '*UNTIL' '(' <until_condition> ')'

<until_condition>     ::= '*SIT' <situation>                                    action => do_until_sit
                      |   '*TTL' <interval>                                     action => do_until_ttl
                      |   '*SIT' <situation> '*OR' '*TTL' <interval>            action => do_until_sit_ttl


<quoted_string>        ~ <single_quoted_string> | <double_quoted_string>

<single_quoted_string> ~ <singlequote> <string_without_single_quote_or_vertical_space> <singlequote>

<null_string>          ~ <singlequote><singlequote>

<double_quoted_string> ~ <doublequote> <string_without_double_quote_or_vertical_space> <doublequote>

<singlequote>          ~ [']

<doublequote>          ~ ["]

<string_without_single_quote_or_vertical_space> ~ [^']+

<string_without_double_quote_or_vertical_space> ~ [^"]+


<enum>                 ~  [*\w]+

<digit>                ~ [\d]

<digits>               ~ [\d]+

<number>               ~ <digits> | <digits>'.'<digits>

<idsit>                ~ <alpha><alphanump>

<alpha>                ~ [A-Za-z]

<alphanump>            ~ [A-Za-z0-9_]*


<id>                  ~ [^\s\.(),'"]+

<literal_word>         ~ [^\s(),'"]+

<digit2>               ~ [0-2]

<digit6>               ~ [0-6]

<hist_sql>              ~ [^\n]*

<interval>             ~ <digits>':'<digit2><digit>':'<digit6><digit>':'<digit6><digit>

#<not_newline>          ~ [^\n]*

ws                     ~ [\s]+

END_OF_DSL

# process the BNF definitions into a Marpa grammer object

my $grammar = Marpa::R2::Scanless::G->new({ source => \$dsl,});

# The situation information have been previously collected
# Marpa is used to trigger a scan. Part of that scan will
# result in action routines being invoked. Those routines
# collect the needed data

for (my $i=0; $i <= $siti; $i++) {
   $curi = $i;
   print "working on $i $sit_pdt[$i]\n" if $opt_v == 1;
   my $recce;
   if ($opt_syntax == 0) {
      $recce = Marpa::R2::Scanless::R->new(
           { grammar => $grammar,
             semantics_package => 'My_Actions',
           });
   } else {
      $recce = Marpa::R2::Scanless::R->new(
           { grammar => $grammar,
             semantics_package => 'My_Actions',
             trace_terminals => 1,
             trace_values => 1,
           });
   }
   #         trace_terminals => 1,                    ## debug
   #         trace_values => 1,                       ## debug
   #### record bad parse and continue on #####        ## todo - manage bad syntax cases
   eval {$recce->read( \$sit_pdt[$i] );};
   if ($@) {
      $sit_syntax[$i] = 1;
      print STDERR "Working on sit[$sit[$i]]\n";
      print STDERR $@ . "\n";
   }

   my $value_ref = $recce->value;
   my $value = $value_ref ? ${$value_ref} : 'No Parse';
   my $progress_report = $recce->show_progress( 0, -1 );
}

# now produce the report of TEMS filtering versus Agent filtering
##                                                     ## todo - determine other bad cases

my $outline;
my $tems_eval;

my $o_file = $opt_workpath . $opt_o;
open OH, ">$o_file" or die "can't open $o_file: $!";

my $a_file = $opt_workpath . "sit_atr.txt";

if ($opt_a == 1) {
   open AH, ">$a_file" or die "can't open $a_file: $!";
}


my $ms_offline_ct = 0;
my $ms_offline_ct_nominal = 5;
my $ms_offline_sits = "";
my $ms_offline_reev_nominal = 300;
my $ms_offline_evals_hour = 0;
my $ms_offline_evals_hour_nominal = 75;
my $in_count_nominal = 12;
my $sit_agent_ct = 0;
my $sit_tems_ct = 0;

if ($opt_a == 1) {
# export situations and  attribute group names
   for (my $i=0; $i<=$siti; $i++) {
      my $sitone = $sit[$i];
      print AH "$sitone $sit_tables[$i]\n";
   }
   close(AH);
}

# first pass to check on subset situations
for (my $i=0; $i<=$siti; $i++) {
   my $sitone = $sit[$i];
   for (my $j=0; $j<=$siti; $j++) {
      next if $i == $j;
      next if length($sitone) < length($sit[$j]);
      next if substr($sitone,0,length($sit[$j])) ne $sit[$j];
      push @{$sit_subset[$i]},$sit[$j];
   }
   if ($sit_fullname[$i] ne "") {
      if ($opt_nofull == 0) {
         if ($sit_fullname[$i] ne $sit[$i]) {
            $sit_psit[$i] = $sit_fullname[$i];
         }
      }
   }
}

# second pass to check on *SIT table attributes
for (my $i=0; $i<=$siti; $i++) {
   next if $sit_sit[$i] == 0;
   my $rc = cycle_sit($i);          # advisory created when looping detected
}

# third pass to update multi-row hash
for (my $i=0; $i<=$siti; $i++) {
   next if $sit_atom[$i] eq "";
   my $tcount = scalar keys %{$sit_alltables[$i]};
   next if $tcount != 1;
   my @groupz = keys %{$sit_alltables[$i]};
   my $group1 = $groupz[0];
   next if defined $multih{$group1};
   $multih{$group1} = "M";
}

# fourth pass to mark multi-row hash conflicts
for (my $i=0; $i<=$siti; $i++) {
   next if $sit_reeval[$i] == 0;       # Ignore pure situations
   next if substr($sit[$i],0,8) eq "UADVISOR";    # ignore history situations
   my $tcount = scalar keys %{$sit_alltables[$i]}; # skip if a single attribute group used
   next if $tcount != 1;
   my @groupz = keys %{$sit_alltables[$i]};        # report only if that single group is considered multi-row
   my $group1 = $groupz[0];
   next if !defined $multih{$group1};
   next if $multih{$group1} eq "S";                 # ignore known single row attribute groups
   next if $sit_atom[$i] ne "";                    # report only if ATOM= is NOT present
   if ($sit_missing[$i] > 0) {                     # skip missing with just one comparand
      next if $sit_missing_ct[$i] == 1;
   }
   $advi++;$advonline[$advi] = "Situation with multi-row attribute group [$group1] but without a DisplayItem";
   $advcode[$advi] = "SITAUDIT1050E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = $sit_psit[$i];
}

# fifth pass to detect several multi-row attribute groups
for (my $i=0; $i<=$siti; $i++) {
   next if $sit_reeval[$i] == 0;       # Ignore pure situations
   next if substr($sit[$i],0,8) eq "UADVISOR";    # ignore history situations
   my $tcount = scalar keys %{$sit_alltables[$i]}; # skip if a single attribute group used
   next if $tcount == 1;
   my $mrows = 0;
   my $matrg = "";
   foreach $f (keys %{$sit_alltables[$i]}) {
      next if !defined $multih{$f};
      next if $multih{$f} eq "S";
      $mrows += 1;
      $matrg .= $f . " ";
   }
   next if $mrows < 2;                    # report only if ATOM= is NOT present
   $advi++;$advonline[$advi] = "Situation with $mrows multi-row attribute groups [$matrg]";
   $advcode[$advi] = "SITAUDIT1052E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = $sit_psit[$i];
   $impossible{$sit[$i]} = "2 or more multi-row attribute groups";
}

# sixth pass to detect BASE/UNTIL with different multi-row attribute groups
for (my $i=0; $i<=$siti; $i++) {
   next if $sit_reeval[$i] == 0;       # Ignore pure situations
   next if substr($sit[$i],0,8) eq "UADVISOR";    # ignore history situations
   next if $sit_until_sit[$i] eq "";
   my $tcount = scalar keys %{$sit_alltables[$i]}; # skip if more than one attribute group
   next if $tcount > 1;
   my @btablek = keys %{$sit_alltables[$i]};
   my $btable = $btablek[0];
   next if !defined $multih{$btable};
   next if $multih{$btable} eq "S";
   my $untilsit = $sit_until_sit[$i];
   my $ux = $sitx{$untilsit};
   next if !defined $ux;
   my @utablek = keys %{$sit_alltables[$ux]};
   my $utable = $utablek[0];
   next if !defined $multih{$utable};
   next if $multih{$utable} eq "S";
   next if $btable eq $utable;
   $advi++;$advonline[$advi] = "Situations with different multi-row attributes on BASE[$btable] and UNTIL[$utable]";
   $advcode[$advi] = "SITAUDIT1057W";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = $sit_psit[$i];
}

for (my $i=0; $i<=$siti; $i++) {


    # calculate number of column functions used
    my $colfunc_ct = $sit_change[$i] +
                     $sit_pctchange[$i] +
                     $sit_count[$i] +
                     $sit_min[$i] +
                     $sit_max[$i] +
                     $sit_avg[$i] +
                     $sit_sum[$i];
    my $colcount_ct = $sit_count[$i] +
                      $sit_min[$i] +
                      $sit_max[$i] +
                      $sit_avg[$i] +
                      $sit_sum[$i];
    if (defined $hSP2OS{$sit[$i]}) {
       $advi++;$advonline[$advi] = "UADVISOR situation may populate hub TEMS virtual table";
       $advcode[$advi] = "SITAUDIT1029W";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
       next;
    }
    if (defined $hProcess{$sit[$i]}) {
       $advi++;$advonline[$advi] = "UADVISOR History collection of Process data";
       $advcode[$advi] = "SITAUDIT1030W";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
       next;
    }
    if (substr($sit[$i],0,8) eq "UADVISOR") {
       next;  # future, need option
       if ($sit_history_collect[$i] eq "CMS") {
          if (substr($sit[$i],0,14) ne "UADVISOR_O4SRV") {
             $advi++;$advonline[$advi] = "Historical Data Collection at TEMS";
             $advcode[$advi] = "SITAUDIT1031I";
             $advimpact[$advi] = $advcx{$advcode[$advi]};
             $advsit[$advi] = $sit_psit[$i];
          }
       }
       if (($sit_history_export[$i] > 0) & ($sit_history_export[$i] != 86400)) {
          if ($opt_sth24 == 1) {
             $advi++;$advonline[$advi] = "Historical Data Collection Export less then 24 hours";
             $advcode[$advi] = "SITAUDIT1032I";
             $advimpact[$advi] = $advcx{$advcode[$advi]};
             $advsit[$advi] = $sit_psit[$i];
          }
       }
       next;
    }
    if ($sit_syntax[$i] == 1) {
       $sit_pdt[$i] = "" if !defined $sit_pdt[$i];
       $advi++;$advonline[$advi] = "Syntax error - [$sit_psit[$i]] [$sit_pdt[$i]]";
       $advcode[$advi] = "SITAUDIT0999E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
       $impossible{$sit[$i]} = "syntax error";
       push(@{$sit_noprivate[$i]},"SyntaxError");
       push(@{$sit_noprivate_FP4[$i]},"SyntaxError");
       push(@{$sit_noprivate_V8[$i]},"SyntaxError");
    }
    if (($sit_autostart[$i] eq "*YES") & ($sit_dist[$i] == 0) & ($opt_nodist == 1)) {
       $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] is Run at Startup but no distribution";
       $advcode[$advi] = "SITAUDIT1019I";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
    }
    if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
       next;
    }
    # domain check
    if (defined $sit_attribs[$siti]) {
       my $x;
       my @dattrib = keys %{$sit_attribs[$siti]};
       if ($#dattrib == 0) {
          my $tattr = $dattrib[0];
          my $domain_ref = $domainx{$tattr};
          if (defined $domain_ref) {
             my $d_type = @{$domain_ref}[0];
             my $d_low = @{$domain_ref}[1];
             my $d_high = @{$domain_ref}[2];
             # Calculate a Perl fragment equal to the predicate test
             my $d_pdt = $sit_pdt[$siti];

             # eliminate the trailing *UNTIL clause if present
             my $ri = rindex($d_pdt,"(");
             if ($ri != -1) {
                if (index(substr($d_pdt,$ri),"*UNTIL") != -1) {
                   $ri--;
                   $d_pdt = substr($d_pdt,0,$ri);
                }
             }
             # now only string types, but could be numeric test
             if ($d_type eq "S") {
                my $d_test;
                my $d_rc;
                $d_pdt = substr($d_pdt,4);    # remove the leading "*IF "
                $d_pdt =~ s/\*VALUE//g;
                my $tattr_meta = quotemeta $tattr;
                $d_pdt =~ s/$tattr_meta/\$d_test/g;
                $d_pdt =~ s/\*EQ/==/g;        # logically should be string compares
                $d_pdt =~ s/\*NE/!=/g;
                $d_pdt =~ s/\*GT/>/g;
                $d_pdt =~ s/\*GE/>=/g;
                $d_pdt =~ s/\*LT/</g;
                $d_pdt =~ s/\*LE/<=/g;
                $d_pdt =~ s/\*AND/and/g;
                $d_pdt =~ s/\*OR/or/g;
                $d_pdt = "\$d_rc = (" . $d_pdt . ")";
                for (my $di=$d_low;$di<=$d_high;$di++) {
                   $d_test = substr("000$di",-2,2);
                   eval ($d_pdt);
                   if ($@) {
                      warn "eval failure $siti $sit[$siti] $d_test $d_pdt";
                   }
                   $sit_domain_pass[$siti] += 1 if $d_rc;

                }
             }
             if ($sit_domain_pass[$siti] == 0) {
                $advi++;$advonline[$advi] = "Situation Formula always evaluates false - $sit_pdt[$siti]";
                $advcode[$advi] = "SITAUDIT1053E";
                $advimpact[$advi] = $advcx{$advcode[$advi]};
                $advsit[$advi] = $sit_psit[$i];
             }
          }
       }
    }
    if (($sit_ms_offline[$i] > 0) or ($sit_ms_online[$i] > 0)) {
       $ms_offline_ct++;
       $ms_offline_sits .= $sit_psit[$i] . " ";
       $ms_offline_evals_hour += 3600/$sit_reeval[$i] if $sit_reeval[$i] > 0;
       if ($sit_reeval[$i] < $ms_offline_reev_nominal) {
          $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] Sampling interval [$sit_reeval[$i] seconds] lower then nominal [$ms_offline_reev_nominal seconds]";
          $advcode[$advi] = "SITAUDIT1007E";
          $advimpact[$advi] = $advcx{$advcode[$advi]};
          $advsit[$advi] = $sit_psit[$i];
       }
       push(@{$sit_noprivate[$i]},"MS_OFFLINE");
       push(@{$sit_noprivate_FP4[$i]},"MS_OFFLINE");
       push(@{$sit_noprivate_V8[$i]},"MS_OFFLINE");
    }
    if ($sit_correlated[$i] > 0) {
       $sit_correlated_ct += 1;
       $sit_correlated_hr += (3600/$sit_reeval[$i])*$sit_correlated[$i] if $sit_reeval[$i] > 0;
    }
    if (($sit_ms_offline[$i] > 0) & ($sit_reason_ne_fa[$i] == 0)) {
       $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] missing Reason *NE FA test";
       $advcode[$advi] = "SITAUDIT1000E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
    }
    if ($sit_ms_online[$i] > 0) {
       $advi++;$advonline[$advi] = "MS_Online type [$sit_psit[$i]]";
       $advcode[$advi] = "SITAUDIT1001E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
    }
    if (($sit_ms_offline[$i] > 0) & ($colfunc_ct > 0)) {
       $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] always just 1";
       $advcode[$advi] = "SITAUDIT1002E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
    }
    if (($sit_ms_offline[$i] > 0) & ($sit_persist[$i] > 1)) {
       $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] with Persist>1";
       $advcode[$advi] = "SITAUDIT1004E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
    }
    if (($sit_ms_offline[$i] > 0) & ($sit_cmd[$i] == 1)) {
       $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] with Action Command";
       $advcode[$advi] = "SITAUDIT1005E";
       $advimpact[$advi] = $advcx{$advcode[$advi]};
       $advsit[$advi] = $sit_psit[$i];
        if (substr($sit_autosopt[$i],2,1) eq "N") {
          $advi++;$advonline[$advi] = "MS_Offline type [$sit_psit[$i]] Action command must be configured to TEMS";
          $advcode[$advi] = "SITAUDIT1006E";
          $advimpact[$advi] = $advcx{$advcode[$advi]};
          $advsit[$advi] = $sit_psit[$i];
       }
    }
   $tems_eval = $sit_scan[$i] +
                $sit_count[$i] +
                $sit_min[$i] +
                $sit_max[$i] +
                $sit_avg[$i] +
                $sit_sum[$i] +
                $sit_pctchange[$i] +
                $sit_time[$i];
   if ($tems_eval == 0) {
     $sit_filter[$i] = "agent";
     $sit_agent_ct += 1;
     $pdtax{$sit_pdt[$i]} = 1;
   }
   if ($tems_eval > 0) {
     $sit_filter[$i] = "tems";
     $sit_tems_ct += 1;
     $pdtax{$sit_pdt[$i]} = 1;
   }
   my @words = split(" ",$sit_tables[$i]);
   for (my $w = 0; $w <=$#words; $w++) {
      my $onetab = $words[$w];
      my $atrg_ref = $Atrg{$onetab};
      if (!defined $atrg_ref) {
         my %ssits = ();
         my %spurs = ();
         my %atrgref = (
                         pure_ct => 0,
                         samp_ct => 0,
                         samp_sits => \%ssits,
                         pure_sits => \%spurs,
                      );
         $Atrg{$onetab} = \%atrgref;
      }
      $sit_tables_ct[$i] += 1;
      if ($sit_reeval[$i] == 0) {
         $Atrg{$onetab}->{pure_ct} += 1;
         $Atrg{$onetab}->{pure_sits}{$sit[$i]} = 1;
      } else {
         $Atrg{$onetab}->{samp_ct} += 1;
         $Atrg{$onetab}->{samp_sits}{$sit[$i]} = 1;
      }
   }
   if ($#words > 0) {
      $advi++;$advonline[$advi] = "Multiple tables in situation [$sit_psit[$i]] tables [$sit_tables[$i]]]";
      $advcode[$advi] = "SITAUDIT1009E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
      push(@{$sit_noprivate[$i]},"MultiTable");
      push(@{$sit_noprivate_FP4[$i]},"MultiTable");
    # EPIC handles *Multiple Tables
    # push(@{$sit_noprivate_V8[$i]},"MultiTable");
   }
   if ($sit_sit[$i] > 0) {
      $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] has *SIT tests";
      $advcode[$advi] = "SITAUDIT1010W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_atrlen[$i] > 0) {
      $advi++;$advonline[$advi] = "Local_Time or Universal_Time test with incorrect attribute length check($sit_atrlen[$i]) [$sit_pdt[$i]";
      $advcode[$advi] = "SITAUDIT1051E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_count[$i] > 1) {
      my @aunique = keys %{$sit_count_attr[$i]};
      my $aprob = 0;
      $aprob += 1 if $#aunique > 0;
      $aprob += 1 if ($sit_and[$i] > 0) and ($sit_or[$i] > 0);
      if ($aprob > 0) {
         $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] has multiple *COUNT tests [$sit_count[$i]]";
         $advcode[$advi] = "SITAUDIT1011E";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit_psit[$i];
         push(@{$sit_noprivate[$i]},"MultiCOUNT");
         push(@{$sit_noprivate_FP4[$i]},"MultiCOUNT");
         push(@{$sit_noprivate_V8[$i]},"MultiCOUNT");
      }
   }
   if ($sit_count_zero[$i] > 0) {
      $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] has *COUNT test against 0";
      $advcode[$advi] = "SITAUDIT1012E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_count_ltone[$i] > 0) {
      $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] has *COUNT test with *LT/*LE 1";
      $advcode[$advi] = "SITAUDIT1013W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_count_lt[$i] > 0) {
      $advi++;$advonline[$advi] = "Situation [$sit_psit[$i]] has *COUNT test with *LT/*LE";
      $advcode[$advi] = "SITAUDIT1014E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_count_process[$i] > 0) {
      $advi++;$advonline[$advi] = "Situation has *COUNT test with Linux/Unix Process_Count attribute";
      $advcode[$advi] = "SITAUDIT1040E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_reeval[$i] == 0) & ($sit_until_sit[$i] ne "")) {
      $advi++;$advonline[$advi] = "Pure Situation [$sit_psit[$i]] has UNTIL/*SIT [$sit_until_sit[$i]]";
      $advcode[$advi] = "SITAUDIT1015W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
      my $usit = $sit_until_sit[$i];
      my $ui = $sitx{$usit};
      if (defined $ui) {
         if (($sit_reeval[$ui] == 0) & ($sit_until_sit[$ui] eq "") & ($sit_until_ttl[$ui] eq "")) {
            $advi++;$advonline[$advi] = "Pure Situation has UNTIL/*SIT [$sit_until_sit[$i]] which is pure sit without any *UNTIL";
            $advcode[$advi] = "SITAUDIT1046E";
            $advimpact[$advi] = $advcx{$advcode[$advi]};
            $advsit[$advi] = $sit_psit[$i];
         }
      }
   }
   if ($sit_reeval[$i] == 0) {
      if ($sit_count[$i] > 0) {
         $advi++;$advonline[$advi] = "Pure Situation [$sit_psit[$i]] has *COUNT test which can cause TEMS instability [$sit_pdt[$i]]";
         $advcode[$advi] = "SITAUDIT1062W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit_psit[$i];
      }
      if ($sit_persist[$i] > 1) {
         $advi++;$advonline[$advi] = "Pure Situation [$sit_psit[$i]] has Persist>1 which can never occur [$sit_pdt[$i]]";
         $advcode[$advi] = "SITAUDIT1063E";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit_psit[$i];
      }
   }
   if ($sit_until_sit[$i] ne "") {
      if ($sit_atom[$i] ne "") {
         my $usit = $sit_until_sit[$i];
         my $ux = $sitx{$usit};
         if (defined $ux) {
            if ($sit_atom[$ux] ne "") {
               if ($sit_atom[$i] ne $sit_atom[$ux]) {
                  $advi++;$advonline[$advi] = "Base Situation uses displayItem[$sit_atom[$i]] and *UNTIL/*SIT [$sit_until_sit[$i]] uses different displayItem[$sit_atom[$ux]]";
                  $advcode[$advi] = "SITAUDIT1048E";
                  $advimpact[$advi] = $advcx{$advcode[$advi]};
                  $advsit[$advi] = $sit_psit[$i];
               }
            }
         }
      }

   }
#  if ($sit_persist[$i] != 1) {
#     push(@{$sit_noprivate[$i]},"Persist");
#     push(@{$sit_noprivate_FP4[$i]},"Persist");
#  }
   if (($sit_reeval[$i] == 0) & ($sit_persist[$i] != 1)) {
      $advi++;$advonline[$advi] = "Pure Situation [$sit_psit[$i]] has Persist>1";
      $advcode[$advi] = "SITAUDIT1016W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_reeval[$i] > 0) & ($sit_until_ttl[$i] ne "")) {
      $advi++;$advonline[$advi] = "Sampled Situation [$sit_psit[$i]] has UNTIL/*TTL [$sit_until_ttl[$i]]";
      $advcode[$advi] = "SITAUDIT1017W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_reeval[$i] > 0) & ($sit_until_sit[$i] ne "") & ($sit_persist[$i] == 1) ) {
      $advi++;$advonline[$advi] = "Sampled Situation [$sit_psit[$i]] with UNTIL/*SIT needs Persist=2";
      $advcode[$advi] = "SITAUDIT1018W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_reeval[$i] > 0) & ($sit_reeval[$i] < 30)) {
      $advi++;$advonline[$advi] = "Sampled Situation [$sit_psit[$i]] less then 30 second sampling time [sit_reeval[$i]]";
      $advcode[$advi] = "SITAUDIT1020W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_min[$i] > 0) | ($sit_max[$i] > 0)) {
      $advi++;$advonline[$advi] = "*MIN/*MAX [$sit_psit[$i]] are unreliable";
      $advcode[$advi] = "SITAUDIT1021W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_ProcessFilter[$i] > 0) & ($colcount_ct > 0)) {
      $advi++;$advonline[$advi] = "Process Filter with numeric column function does not work";
      $advcode[$advi] = "SITAUDIT1034W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_fileinfo_path[$i] > 0) & ($sit_fileinfo_file[$i] == 0)) {
      $advi++;$advonline[$advi] = "Situation formula with Path and no File in formula";
      $advcode[$advi] = "SITAUDIT1054E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (($sit_nteventlog_logname[$i] == 0) & ($sit_nteventlog_eventid[$i] > 0)) {
      $advi++;$advonline[$advi] = "NT_Event_Log Situation formula without Log_Name";
      $advcode[$advi] = "SITAUDIT1055W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_alwaystrue[$i] > 0) {
      $advi++;$advonline[$advi] = "*VALUE test with always true *GE 0 test pdt[$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1035W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_scan_ne[$i] > 0) {
      $advi++;$advonline[$advi] = "*SCAN with *NE check works like a *VALUE *NE test pdt[$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1036W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_time_same[$i] > 0) {
      $advi++;$advonline[$advi] = "*TIME [$sit_psit[$i]] same attribute group tested";
      $advcode[$advi] = "SITAUDIT1022W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
      $impossible{$sit[$i]} = "TIME test with same attribute group";
   }
   if (($sit_cmd[$i] == 1) & ($sit_reeval[$i] > 0)) {
      if (length($sit_autosopt[$i]) == 3) {
         if (substr($sit_autosopt[$i],1,1) eq "Y") {
            if (substr($sit_autosopt[$i],2,1) eq "N") {
               $advi++;$advonline[$advi] = "Sampled Situation [$sit_psit[$i]] with Action Command running every interval";
               $advcode[$advi] = "SITAUDIT1023W";
               $advimpact[$advi] = $advcx{$advcode[$advi]};
               $advsit[$advi] = $sit_psit[$i];
            } else {
               $advi++;$advonline[$advi] = "Sampled Situation [$sit_psit[$i]] with Action Command on TEMS running every interval";
               $advcode[$advi] = "SITAUDIT1024E";
               $advimpact[$advi] = $advcx{$advcode[$advi]};
               $advsit[$advi] = $sit_psit[$i];
            }
         }
      }
   }
   if (($sit_process[$i] > 0) & ($colcount_ct > 0)) {
      $advi++;$advonline[$advi] = "Arithmetic test on Process situation [$sit_psit[$i]] [$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1025W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   } elsif (($sit_fileinfo[$i] > 0) & ($colcount_ct > 0)) {
      $advi++;$advonline[$advi] = "Arithmetic test on File Information situation [$sit_psit[$i]] [$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1026W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   } elsif  (($sit_atom[$i] ne "") & ($colcount_ct > 0)) {
      $advi++;$advonline[$advi] = "Arithmetic test on Multi-row attribute group [$sit_psit[$i]] [$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1027W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
#  if ($sit_atom[$i] ne ""){
#     push(@{$sit_noprivate[$i]},"DisplayItem");
#     push(@{$sit_noprivate_FP4[$i]},"DisplayItem");
#  }
#  if (length($sit_dst[$i]) > 0){
#     if ($sit_dst[$i] ne "0") {
#        push(@{$sit_noprivate[$i]},"EventDest!=0");
#        push(@{$sit_noprivate_FP4[$i]},"EventDest!=0");
#     }
#  }
   if (substr($sit_cmdtext[$i],0,5) ne '*NONE') {
      if (index($sit_cmdtext[$i],'&{') != -1) {
         my $tcmd = $sit_cmdtext[$i];
         my $bad_tables = " ";
         my $nt_desc_ct = 0;
         while ($tcmd =~ m/\&\{(.*?)\}/g) {
            my $subst = $1;
            next if defined $hBuiltIn{$subst};
            if (($subst eq "NT_Event_Log.Description") or ($subst eq "NT_Event_Log.Description_U")){
              $nt_desc_ct += 1;
            }
            $subst =~ /(.*?)\./;
            my $sub_group = $1;
            next if defined $sit_alltables[$i]{$sub_group};
            $bad_tables .= $sub_group . " " if index($bad_tables,$sub_group) == -1;
         }
         if ($bad_tables ne " ") {
            $advi++;$advonline[$advi] = "Action command attribute group(s) [$bad_tables] not present in Situation Formula";
            $advcode[$advi] = "SITAUDIT1028E";
            $advimpact[$advi] = $advcx{$advcode[$advi]};
            $advsit[$advi] = $sit_psit[$i];
         }
         if ($nt_desc_ct > 0) {
            $advi++;$advonline[$advi] = "Action Command substitution NT_Event_Log Description/Description_U";
            $advcode[$advi] = "SITAUDIT1041W";
            $advimpact[$advi] = $advcx{$advcode[$advi]};
            $advsit[$advi] = $sit_psit[$i];
         }
      }
      if (length($sit_autosopt[$i]) == 3) {
         if (substr($sit_autosopt[$i],1,1) eq "Y") {
            push(@{$sit_noprivate[$i]},"ActionCommandTEMS");
            push(@{$sit_noprivate_FP4[$i]},"ActionCommandTEMS");
            push(@{$sit_noprivate_V8[$i]},"ActionCommandTEMS");
         }
      }
   }

   if (($sit_change[$i] > 0) & ($sit_in[$i] > 0)) {
      $advi++;$advonline[$advi] = "*IN and *CHANGE together in a situation formula can cause TEMS crash until before ITM 623 FP2";
      $advcode[$advi] = "SITAUDIT1042W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }

   if ($sit_inct[$i] > $in_count_nominal) {
      $advi++;$advonline[$advi] = "Count of *IN values $sit_inct[$i] greater then nominal $in_count_nominal";
      $advcode[$advi] = "SITAUDIT1043W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }

   if ($sit_utfwild[$i] > 0) {
      if ($sit_reeval[$i] > 0 ) {
         $advi++;$advonline[$advi] = "Unicode attribute with wildcard [*] value tests";
         $advcode[$advi] = "SITAUDIT1044W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit_psit[$i];
      }
   }

   if ($sit_timeneeq[$i] > 0) {
      $advi++;$advonline[$advi] = "*TIME delta test with *EQ or *NE which is never correct - pdt[$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1058E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
      $impossible{$sit[$i]} = "TIME test with *EQ or *NE";
   }

   if ($sit_timefuture[$i] > 0) {
      $advi++;$advonline[$advi] = "*TIME delta test which implies test for future time [$sit_pdt[$i]]";
      $advcode[$advi] = "SITAUDIT1059W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }

   if (defined $sit_subset[$i]) {
      if ((scalar @{$sit_subset[$i]}) > 0) {
         my $psits = join(" ",@{$sit_subset[$i]});
         $advi++;$advonline[$advi] = "Situation a superset of other sits [$psits]";
         $advcode[$advi] = "SITAUDIT1037I";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit_psit[$i];
      }
   }
   if ($sit_reeval_bad_days[$i] == 1) {
      $advi++;$advonline[$advi] = "Situation Reevaluate days must be 1 to 3 characters long";
      $advcode[$advi] = "SITAUDIT1038W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if ($sit_reeval_bad_time[$i] == 1) {
      $advi++;$advonline[$advi] = "Situation Reevaluate time must be 6 characters long";
      $advcode[$advi] = "SITAUDIT1039W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
   }
   if (substr($sit_pdt[$i],0,4) ne "*IF ") {
      $advi++;$advonline[$advi] = "Situation Predicate not starting with *IF and blank";
      $advcode[$advi] = "SITAUDIT0999E";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = $sit_psit[$i];
      $impossible{$sit[$i]} = "syntax not starting with *IF";
   }
   if (($sit_and[$i] > 0) and ($sit_or[$i] > 0)) {
      push(@{$sit_noprivate[$i]},"AND+OR");
      push(@{$sit_noprivate_FP4[$i]},"AND+OR");

    # EPIC handles *AND+OR
    # push(@{$sit_noprivate_V8[$i]},"AND+OR");
   }
   if ($sit_and[$i] > 9) {
      push(@{$sit_noprivate[$i]},"AND>9");
      push(@{$sit_noprivate_FP4[$i]},"AND>9");
    # EPIC handles *AND>9
    # push(@{$sit_noprivate_V8[$i]},"AND>9");
   }
   if ($sit_or[$i] > 10) {
      push(@{$sit_noprivate[$i]},"OR>10");
      push(@{$sit_noprivate_FP4[$i]},"OR>10");
    # EPIC handles *OR>10
    # push(@{$sit_noprivate_V8[$i]},"OR>10");
   }
   # Event Mapping implemented using agent side xml files

#  if (defined $hevmap{$sit[$i]}) {
#     push(@{$sit_noprivate[$i]},"EventMap");
#     push(@{$sit_noprivate_FP4[$i]},"EventMap");
#     push(@{$sit_noprivate_V8[$i]},"EventMap");
#  }
   if (defined $hactp{$sit[$i]}) {
      push(@{$sit_noprivate[$i]},"Policy");
      push(@{$sit_noprivate_FP4[$i]},"Policy");
      push(@{$sit_noprivate_V8[$i]},"Policy");
   }
   if (defined $hovrd{$sit[$i]}) {
      push(@{$sit_noprivate[$i]},"Override");
      push(@{$sit_noprivate_FP4[$i]},"Override");
      push(@{$sit_noprivate_V8[$i]},"Override");
   }
   if ($sit_fullname[$i] ne "") {
      if ($sit_fullname[$i] ne $sit[$i]) {
         push(@{$sit_workprivate[$i]},"Longname");
         push(@{$sit_workprivate_FP4[$i]},"Longname");
         push(@{$sit_workprivate_V8[$i]},"Longname");
      }
   }
   if ($sit_reeval[$i] >= 86400) {
      push(@{$sit_noprivate[$i]},"IntervalDays");
      push(@{$sit_noprivate_FP4[$i]},"IntervalDays");
      push(@{$sit_noprivate_V8[$i]},"IntervalDays");
   }
}

if ($sit_correlated_ct > 0){
   if ($sit_correlated_hr >= 12) {
      $advi++;$advonline[$advi] = "Correlated Situations [$sit_correlated_ct] ISITSTSH scans [$sit_correlated_hr] per hour - more than 12";
      $advcode[$advi] = "SITAUDIT1056W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "correlated";
   }
}

if ($ms_offline_ct > $ms_offline_ct_nominal) {
   $advi++;$advonline[$advi] = "Too many MS_Offline type situations [$ms_offline_ct] vs nominal [$ms_offline_ct_nominal]] sits[$ms_offline_sits]";
   $advcode[$advi] = "SITAUDIT1003E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "";
}

if (($ms_offline_ct > 0) & ($ms_offline_evals_hour > $ms_offline_evals_hour_nominal)) {
   $advi++;$advonline[$advi] = "Too many MS_Offline evaluations per hour [$ms_offline_evals_hour] nominal [$ms_offline_evals_hour_nominal]";
   $advcode[$advi] = "SITAUDIT1008E";
   $advimpact[$advi] = $advcx{$advcode[$advi]};
   $advsit[$advi] = "";
}
if ($sit_tems_alert == 1) {
   if (($sit_tems_alert_run == 0) or ($sit_tems_alert_dist == 0)) {
      $advi++;$advonline[$advi] = "TEMS_Alert defined but not running";
      $advcode[$advi] = "SITAUDIT1033W";
      $advimpact[$advi] = $advcx{$advcode[$advi]};
      $advsit[$advi] = "TEMS_Alert";
   }
}

foreach $f (sort { $a cmp $b } keys %Atrg) {
   my $sx;
   if (($Atrg{$f}->{pure_ct} > 0) and ($Atrg{$f}->{samp_ct} > 0)) {
      if (($Atrg{$f}->{samp_ct} > $Atrg{$f}->{pure_ct})) {  # mostly sampled
         foreach my $g (keys %{$Atrg{$f}->{pure_sits}}) {
            $sx = $sitx{$g};
            next if !defined $sx;
            next if $sit_tables_ct[$sx] == 1;
            if ($sit_reeval[$sx] == 0) {
               $advi++;$advonline[$advi] = "Attribute Group [$f] coerced from Sampled to Pure in sit[$g] pdt[$sit_pdt[$sx]]";
               $advcode[$advi] = "SITAUDIT1061E";
               $advimpact[$advi] = $advcx{$advcode[$advi]};
               $advsit[$advi] = $f;
            }
         }
      } else {                                             # mostly pure
         foreach my $g (keys %{$Atrg{$f}->{samp_sits}}) {
            $sx = $sitx{$g};
            next if !defined $sx;
            next if $sit_tables_ct[$sx] == 1;
            if ($sit_reeval[$sx] > 0) {
               $advi++;$advonline[$advi] = "Attribute Group [$f] coerced from Sampled to Pure in sit[$g] pdt[$sit_pdt[$sx]]";
               $advcode[$advi] = "SITAUDIT1047E";
               $advimpact[$advi] = $advcx{$advcode[$advi]};
               $advsit[$advi] = $f;
            }
         }
      }
   }
}

if ($opt_nohdr == 0){
   print OH "Situation Audit Report $gVersion\n";
   print OH "Start: $sitaudit_start_time\n";
   print OH "\n";
}

$rptkey = "SITREPORT001";$advrptx{$rptkey} = 1;         # record report key
my $tsit = $siti + 1;
print OH "$rptkey: Summary Report\n";
print OH "Total Situations,$tsit\n";
my $pdt_ct = scalar keys %pdtx;
print OH "Total Situation Formula,$pdt_ct\n";
$tsit = $sit_tems_ct + $sit_agent_ct;
print OH "Total Active Situations,$tsit\n";
my $pdta_ct = scalar keys %pdtax;
print OH "Total Active Situation Formula,$pdta_ct\n";
$tsit = $advi + 1;
print OH "Advisory messages,$tsit\n";
print OH "Filter at TEMS,$sit_tems_ct\n";
print OH "Filter at Agent,$sit_agent_ct\n";

print OH "\n";
$rptkey = "SITREPORT002";$advrptx{$rptkey} = 1;         # record report key
print OH "$rptkey: Top 20 most recently added or changed Situations\n";
print OH "LSTDATE,Situation,Formula\n";
my $top20 = 0;
foreach $f ( sort { $sit_lstdate[$sitx{$b}] cmp $sit_lstdate[$sitx{$a}] ||
                       $sit_psit[$sitx{$a}] cmp $sit_psit[$sitx{$b}]
                     } keys %sitx) {
   $top20 += 1;
   my $j = $sitx{$f};
   print OH "$sit_lstdate[$j],$sit_psit[$j],$sit_pdt[$j],\n";
   last if $top20 >= 20;
}

if ($advi != -1) {
   print OH "\n";
   print OH "Advisory Message Report - *NOTE* See advisory notes at report end\n";
   print OH "Impact,Advisory Code,Situation,Advisory\n";
   for (my $a=0; $a<=$advi; $a++) {
       my $mysit = $advsit[$a];
       my $myimpact = $advimpact[$a];
       my $mykey = $mysit . "|" . $a;
       $advx{$mykey} = $a;
   }
   foreach $f ( sort { $advimpact[$advx{$b}] <=> $advimpact[$advx{$a}] ||
                          $advcode[$advx{$a}] cmp $advcode[$advx{$b}] ||
                          $advsit[$advx{$a}] cmp $advsit[$advx{$b}] ||
                          $advonline[$advx{$a}] cmp $advonline[$advx{$b}]
                        } keys %advx ) {
      my $j = $advx{$f};
      next if $advimpact[$j] == -1;
      my $skipone = $advcode[$j];
      next if defined $hSkip{$skipone};
      print OH "$advimpact[$j],$advcode[$j],$advsit[$j],$advonline[$j]\n";
      $advgotx{$advcode[$j]} = $advimpact[$j]
   }
} else {
   print OH "No Expert Advisory messages\n";
}

print OH "\n";
$rptkey = "SITREPORT003";$advrptx{$rptkey} = 1;         # record report key
print OH "$rptkey: Situations with TEMS Filtering Report\n";
print OH "Fullname,Filter,PDT\n";
for (my $i=0; $i<=$siti; $i++) {
    next if $sit_syntax[$i] == 1;
    next if $sit_filter[$i] eq "agent";
    next if  $sit_dist_objaccl[$i] eq "";
    next if substr($sit[$i],0,8) eq "UADVISOR";
    $outline = "$sit_psit[$i]," . "tems," . "\"" . $sit_pdt[$i] . "\"";
    print OH "$outline\n";
}

if ($opt_agent_filter == 1) {
   $rptkey = "SITREPORT004";$advrptx{$rptkey} = 1;         # record report key
   print OH "\n";
   print OH "$rptkey: Situations with Agent Filtering Report\n";
   print OH "Fullname,Filter,PDT\n";
   for (my $i=0; $i<=$siti; $i++) {
       next if $sit_syntax[$i] == 1;
       next if $sit_filter[$i] eq "tems";
       next if  $sit_dist_objaccl[$i] eq "";
       next if substr($sit[$i],0,8) eq "UADVISOR";
       $outline = "$sit_psit[$i]," . "agent," . "\"" . $sit_pdt[$i] . "\"";
       print OH "$outline\n";
   }
}
if ($opt_dist == 1) {
   $rptkey = "SITREPORT005";$advrptx{$rptkey} = 1;         # record report key
   print OH "\n";
   print OH "$rptkey: Situation with Distributions Report\n";
   print OH "Situation,Autostart,Distribution\n";
   for (my $i=0; $i<=$siti; $i++) {
       next if  $sit_dist_objaccl[$i] eq "";
       next if substr($sit[$i],0,8) eq "UADVISOR";
       $outline = $sit_psit[$i] . ",";
       $outline .= $sit_autostart[$i] . ",";
       $outline .= $sit_dist_objaccl[$i];
       print OH "$outline\n";
   }
}

if ($opt_dist == 1) {
   $rptkey = "SITREPORT005";$advrptx{$rptkey} = 1;         # record report key
   print OH "\n";
   print OH "$rptkey: Situation with Distributions Report\n";
   print OH "Situation,Autostart,Distribution\n";
   for (my $i=0; $i<=$siti; $i++) {
       next if  $sit_dist_objaccl[$i] eq "";
       next if substr($sit[$i],0,8) eq "UADVISOR";
       $outline = $sit_psit[$i] . ",";
       $outline .= $sit_autostart[$i] . ",";
       $outline .= $sit_dist_objaccl[$i];
       print OH "$outline\n";
   }
}

if ($sit_correlated_ct > 0) {
   $rptkey = "SITREPORT008";$advrptx{$rptkey} = 1;         # record report key
   print OH "\n";
   print OH "$rptkey: Correlated Situations Report\n";
   print OH "Situation,Sampling,PDT,\n";
   for (my $i=0; $i<=$siti; $i++) {
       next if  $sit_correlated[$i] == 0;
       $outline = $sit_psit[$i] . ",";
       $outline .= $sit_reeval[$i] . ",";
       $outline .= $sit_pdt[$i] . ",";
       print OH "$outline\n";
   }
}


# Calculate situations with duplicate PDTs
$rptkey = "SITREPORT006";$advrptx{$rptkey} = 1;         # record report key
print OH "\n";
print OH "Situation Formula appearing in more than $opt_pdtlim situations\n";
print OH "PDT,\n";
print OH ",Count,Situations\n";
my $pdt_total = 0;
my $sitpdt_total = 0;
foreach $f (sort { $pdtx{$b}->{count} <=> $pdtx{$a}->{count} ||
                      $a cmp $b
                    } keys %pdtx) {
   my $pdt_ref = $pdtx{$f};
   last if $pdt_ref->{count} <= $opt_pdtlim;
   $pdt_total += 1;
   $sitpdt_total += $pdt_ref->{count};
   print OH $f . ",\n";
   $oneline = "," . $pdt_ref->{count} . ",";
   my $psits = join(" ",@{$pdt_ref->{sits}});
   $oneline .= $psits;
   print OH "$oneline\n";
}

# when there are duplicate PDTs, if desired create .sh and .cmd files
# to generate new MSLs and also to delete obsolete situations
if ($pdt_total > 0) {
   if ($opt_pdtmsl == 1) {
      my $mslfilesh = "sitaudit_msl.sh";
      my $mslfilecmd = "sitaudit_msl.cmd";
      my $delsitsh = "sitaudit_del.sh";
      my $delsitcmd = "sitaudit_del.cmd";
      my $mslsh;
      my $mslcmd;
      my $delsh;
      my $delcmd;
      open $mslsh, ">$mslfilesh" or die "can't open $mslfilesh: $!";
      binmode($mslsh);
      open $mslcmd, ">$mslfilecmd" or die "can't open $mslfilecmd: $!";
      open $delsh, ">$delsitsh" or die "can't open $delsitsh: $!";
      binmode($delsh);
      open $delcmd, ">$delsitcmd" or die "can't open $delsitcmd: $!";
      my $outl;
      my @sits;
      my %pdt_agents;
      foreach $f (sort { $pdtx{$b}->{count} <=> $pdtx{$a}->{count} ||
                            $a cmp $b
                          } keys %pdtx) {
         my $pdt_ref = $pdtx{$f};
         last if $pdt_ref->{count} <= $opt_pdtlim;
         @sits = @{$pdt_ref->{sits}};
         %pdt_agents = ();
         for (my $s=0;$s<=$#sits;$s++) {
            my $sit1 = $sits[$s];
            $sx = $sitx{$sit1};
            next if !defined $sx;
            my @dists = split(" ",$sit_dist_objaccl[$sx]);
            for (my $d=0; $d<= $#dists; $d++) {
               my $dist1 = substr($dists[$d],5);
               my $target = $nodel{$dist1};
               if (!defined $target) {
                  $pdt_agents{$dist1} = 1;
               } else {
                  foreach my $g (keys %{$target->{nodes}}) {
                     $pdt_agents{$g} = 1;
                  }
               }
           }
        }
         # finished a cycle for one pdt
         #
         my $sitbase = $sits[0];
         my $agentbase;
         my $agent_pc;

         # needed because sometimes a distribution is defined but agent not in TNODESAV, perhaps offline
         foreach my $ff (keys %pdt_agents) {
            next if !defined $nsav{$ff};
            $agentbase = $ff;
            $agent_pc = $nsav{$ff};
            last;
         }
         next if !defined $agentbase;
         my $listbase = $sitbase . "_model_systemlist";
         my $outsh = "./tacmd createsystemlist -t " . $agent_pc . " -l " .  $listbase . " -m ";
         my $outcmd = "tacmd createsystemlist -t " . $agent_pc . " -l " .  $listbase . " -m ";
         my $mcount = 0;
         foreach my $h (keys %pdt_agents) {
            $outsh .= $h . " ";
            $outcmd.= $h . " ";
            $mcount += 1;
            next if $mcount < 5;
            printf $mslsh "$outsh\n";
            printf $mslcmd "$outcmd\n";
            $mcount = 0;
            $outsh = "./tacmd editesystemlist -f -l " . $listbase . " -add ";
            $outcmd = "tacmd editesystemlist -f -l " .  $listbase . " -add ";
         }
         if ($mcount > 0) {
            printf $mslsh "$outsh\n";
            printf $mslcmd "$outcmd\n";
         }
         printf $delsh "# Other situations associated with $listbase\n ";
         printf $delcmd "*rem Other situations associated with $listbase\n ";
         for (my $t=0; $t<=$#sits; $t++) {
            my $sit1 = $sits[$t];
            next if $sit1 eq $sitbase;
            printf $delsh "./tacmd deletesit -f -s " . $sit1 . "\n ";
            printf $delcmd "tacmd deletesit -f -s " . $sit1 . "\n ";
         }
         printf $delsh "#\n";
         printf $delcmd "*rem\n";

      }
      close $mslsh;
      close $mslcmd;
      close $delsh;
      close $delcmd;
   }
}

# when wanted print out the sitname, fullname and pdt
if ($pdt_total > 0) {
   if ($opt_sitpdt == 1) {
      my $sitfilecmd = "sitaudit_pdt.csv";
      my $sitcmd;
      open $sitcmd, ">$sitfilecmd" or die "can't open $sitfilecmd: $!";
      my $outl;
      my $s;
      for (my $i=0; $i<=$siti; $i++) {
         next if $sit_autostart[$i] ne "*YES";
         $outl = $sit[$i] . "\t";
         $outl .= $sit_fullname[$i]  . "\t";
         $outl .= $sit_reeval[$i]  . "\t";
         $outl .= $sit_pdt[$i]  . "\t";
         print $sitcmd "$outl\n";
      }
      close $sitcmd;
   }
}
my $im_ct = scalar keys %impossible;
if ($im_ct > 0) {
   my $noautosh;
   my $noautocmd;
   open $noautosh, ">noauto.sh" or die "can't open noauto.sh: $!";
   binmode($noautosh);
   open $noautocmd, ">noauto.cmd" or die "can't open noauto.cmd: $!";
   foreach $f (keys %impossible) {
      printf $noautosh "# " . $impossible{$f} . "\n";
      printf $noautosh "./tacmd editSit -s $f -p RunOnStart=No -f\n";
      printf $noautocmd "*REM " . $impossible{$f} . "\n";
      printf $noautocmd "tacmd editSit -s $f -p RunOnStart=No -f\n";
   }
   close($noautosh);
   close($noautocmd);
}

# first pass to check on subset situations
if ($opt_nofull == 1) {
   $rptkey = "SITREPORT007";$advrptx{$rptkey} = 1;         # record report key
   print OH "\n";
   print OH "Sitname Fullname Summary\n";
   print OH "sitname,fullname,\n";
   for (my $i=0; $i<=$siti; $i++) {
      next if $sit_fullname[$i] eq "";
      next if $sit_fullname[$i] eq $sit[$i];
      print OH $sit[$i] . "," . $sit_fullname[$i] . "\n";
   }
}



#if ($pdt_total > 0) {
#   my $rate_pdt = $sitpdt_total/$pdt_total;
#   if ($rate_pdt > 1) {
#      $advi++;$advonline[$advi] = "Situation Formula being used for more than $pdt_situations_nominal - pdt[$pdt_total] sits[$sitpdt_total] avg[$rate_pdt] See report";
#      $advcode[$advi] = "DATAHEALTH1090W";
#      $advimpact[$advi] = $advcx{$advcode[$advi]};
#      $advsit[$advi] = "PDT";
#
#   }
#}

my $prv_pass_total = 0;
my $prv_passfp4_total = 0;
my $prv_passv8_total = 0;
my $prv_fail_total = 0;
my $prv_fail_totalfp4 = 0;
my $prv_fail_totalv8 = 0;
my $prv_work_total = 0;
my $prv_work_totalfp4 = 0;
my $prv_work_totalv8 = 0;
my @noprivate_reasons = ();
my @workprivate_reasons = ();
my %phash = ();
my @punique = ();
my $preason;
my $fraction;
my $pfraction;


if ($opt_private == 1) {    # private situation audit report wanted
   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate[$i]};
      @workprivate_reasons =  @{$sit_workprivate[$i]};
      if (($#noprivate_reasons == -1) and  ($#workprivate_reasons == -1)) {
         $prv_pass_total += 1;
         next;
      }
      if ($#noprivate_reasons != -1) {
         $prv_fail_total += 1;
         %phash   = map { $_, 1 } @noprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_reasons{$preason}) {
               $hprivate_reasons{$preason} += 1;
            } else {
               print STDERR "unknown private reason $preason sit[$sit[$i]]\n";
            }
         }
      }
      if ($#workprivate_reasons != -1) {
         $prv_work_total += 1;
         %phash   = map { $_, 1 } @workprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_work{$preason}) {
               $hprivate_work{$preason} += 1;
            } else {
               print STDERR "unknown private work reason $preason sit[$sit[$i]]\n";
            }
         }
      }
   }

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate_FP4[$i]};
      @workprivate_reasons =  @{$sit_workprivate_FP4[$i]};
      if (($#noprivate_reasons == -1) and  ($#workprivate_reasons == -1)) {
         $prv_passfp4_total += 1;
         next;
      }
      if ($#noprivate_reasons != -1) {
         $prv_fail_totalfp4 += 1;
         %phash   = map { $_, 1 } @noprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_reasons{$preason}) {
               $hprivate_reasons_FP4{$preason} += 1;
            } else {
               print STDERR "unknown private reason FP4 $preason sit[$sit[$i]]\n";
            }
         }
      }
      if ($#workprivate_reasons != -1) {
         $prv_work_totalfp4 += 1;
         %phash   = map { $_, 1 } @workprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_work_FP4{$preason}) {
               $hprivate_work_FP4{$preason} += 1;
            } else {
               print STDERR "unknown private work reason FP4 $preason sit[$sit[$i]]\n";
            }
         }
      }
   }

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate_V8[$i]};
      @workprivate_reasons =  @{$sit_workprivate_V8[$i]};
      if (($#noprivate_reasons == -1) and  ($#workprivate_reasons == -1)) {
         $prv_passv8_total += 1;
         next;
      }
      if ($#noprivate_reasons != -1) {
         $prv_fail_totalv8 += 1;
         %phash   = map { $_, 1 } @noprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_reasons{$preason}) {
               $hprivate_reasons_V8{$preason} += 1;
            } else {
               print STDERR "unknown private reason V8 $preason sit[$sit[$i]]\n";
            }
         }
      }
      if ($#workprivate_reasons != -1) {
         $prv_work_totalv8 += 1;
         %phash   = map { $_, 1 } @workprivate_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hprivate_work_V8{$preason}) {
               $hprivate_work_V8{$preason} += 1;
            } else {
               print STDERR "unknown private work reason V8 $preason sit[$sit[$i]]\n";
            }
         }
      }
   }


   print OH "\n";
   print OH "Private Situation Audit\n";
   $tsit = $siti+1;
   print OH "Total Situations,$tsit\n";
   $tsit = $sit_tems_ct + $sit_agent_ct;
   print OH "Total Active Situations,$tsit\n";

   $pcount = $prv_pass_total;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Passing Private Situations,$prv_pass_total,$pfraction%\n";

   $pcount = $prv_work_total;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Need Work Private Situations,$prv_work_total,$pfraction%\n";

   $pcount = $prv_passfp4_total;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Passing Private Situations at ITM 630 FP4,$prv_passfp4_total,$pfraction%\n";

   $pcount = $prv_work_totalfp4;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Need Work Private Situations at ITM 630 FP4,$prv_work_totalfp4,$pfraction%\n";

   $pcount = $prv_passv8_total;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Passing Private Situations at V8,$prv_passv8_total,$pfraction%\n";

   $pcount = $prv_work_totalv8;
   $fraction = ($pcount*100) / $tsit;
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Need Work Private Situations at V8,$prv_work_totalv8,$pfraction%\n";

   $pcount = $sit_tems_ct;
   $fraction = ($pcount*100) / ($sit_tems_ct+$sit_agent_ct);
   $pfraction = sprintf "%.2f", $fraction;
   print OH "Active Situations filtered at the TEMS,$sit_tems_ct,$pfraction%\n";


   print OH "\n";
   print OH "NoPrivateReason_Current,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_reasons ) {
      $pcount = $hprivate_reasons{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_fail_total if $prv_fail_total > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "WorkPrivateReason_Current,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_work ) {
      $pcount = $hprivate_work{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_work_total if $prv_work_total > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "NoPrivateReason_FP4,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_reasons_FP4 ) {
      $pcount = $hprivate_reasons_FP4{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_fail_totalfp4 if $prv_fail_totalfp4 > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "WorkPrivateReason_FP4,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_work_FP4 ) {
      $pcount = $hprivate_work_FP4{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_work_totalfp4 if $prv_work_totalfp4 > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "NoPrivateReason_V8,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_reasons_V8 ) {
      $pcount = $hprivate_reasons_V8{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_fail_totalv8 if $prv_fail_totalv8 > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "WorkPrivateReason_V8,Count,PerCent\n";
   foreach $f ( sort { $a cmp $b } keys %hprivate_work_V8 ) {
      $pcount = $hprivate_work_V8{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $prv_work_totalv8 if $prv_work_totalv8 > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations failing Current\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations need work Current\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_workprivate[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations failing FP4\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate_FP4[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations need work FP4\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_workprivate_FP4[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations failing V8\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_noprivate_V8[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "Private Situations need work V8\n";
   print OH "Situation,Reasons,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @noprivate_reasons =  @{$sit_workprivate_V8[$i]};
      next if $#noprivate_reasons == -1;
      $outline = $sit_psit[$i] . ",";
      $outline .= join("|",@noprivate_reasons) . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }

   print OH "\n";
   print OH "All Situations\n";
   print OH "Situation,Current,FP4,V8,PDT\n";

   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      $outline = $sit_psit[$i] . ",";
      my $status = "ok";
      @noprivate_reasons =  @{$sit_noprivate[$i]};
      if ($#noprivate_reasons != -1) {
         $status = "fail";
      }
      $outline .= $status . ",";
      $status = "ok";
      @noprivate_reasons =  @{$sit_noprivate_FP4[$i]};
      if ($#noprivate_reasons != -1) {
        $status = "fail";
      }
      $outline .= $status . ",";
      $status = "ok";
      @noprivate_reasons =  @{$sit_noprivate_V8[$i]};
      if ($#noprivate_reasons != -1) {
         $status = "fail";
      }
      $outline .= $status . ",";
      $outline .= '"' . $sit_pdt[$i] . '",';
      print OH "$outline\n";
   }
}

my @function_reasons = ();
my $sit_function_total = 0;

if ($opt_function == 1) {
   for (my $i=0;$i<=$siti;$i++) {
      next if substr($sit[$i],0,8) eq "UADVISOR";
      if (($sit_dist[$i] == 0) & ($opt_nodist == 0 ) & ($sit_distribution == 1)) {
         next;
      }
      @function_reasons =  @{$sit_function[$i]};
      if ($#function_reasons != -1) {
         $sit_function_total += 1;
         %phash   = map { $_, 1 } @function_reasons;
         @punique = keys %phash;
         for (my $j=0;$j<=$#punique;$j++) {
            $preason = $punique[$j];
            if (defined $hfunction{$preason}) {
               $hfunction{$preason} += 1;
            } else {
               print STDERR "unknown function $preason sit[$sit[$i]]\n";
            }
         }
         next;
      }
   }

   print OH "\n";
   print OH "Situaton Function Audit\n";
   $tsit = $siti+1;
   print OH "Total Situations,$tsit\n";
   $tsit = $sit_tems_ct + $sit_agent_ct;
   print OH "Total Active Situations,$tsit\n";

   print OH "\n";
   print OH "Function,Count,PerCent\n";
   foreach $f ( sort { $hfunction{$b} <=> $hfunction{$a} } keys %hfunction ) {
      $pcount = $hfunction{$f};
      $fraction = 0;
      $fraction = ($pcount*100) / $sit_function_total if $sit_function_total > 0;
      $pfraction = sprintf "%.2f", $fraction;
      $outline = $f . ",";
      $outline .= $pcount . ",";
      $outline .= $pfraction . "%,";
      print OH "$outline\n";
   }
}
if ($advi != -1) {
   print OH "\n";
   print OH "Advisory Trace, Meaning and Recovery suggestions follow\n\n";
   foreach $f ( sort { $a cmp $b } keys %advgotx ) {
      next if substr($f,0,8) ne "SITAUDIT";
      print OH "Advisory code: " . $f  . "\n";
      print OH "Impact:" . $advgotx{$f}  . "\n";
      print STDERR "$f missing\n" if !defined $advtextx{$f};
      print OH $advtextx{$f};
   }
}

my $rpti = scalar keys %advrptx;
if ($rpti != -1) {
   print OH "\n";
   print OH "Situation Audit Reports - Meaning and Recovery suggestions follow\n\n";
   foreach $f ( sort { $a cmp $b } keys %advrptx ) {
      next if !defined $advrptx{$f};
      print STDERR "$f missing\n" if !defined $advtextx{$f};
      print OH "$f\n";
      print OH $advtextx{$f};
   }
}
print OH "\n";
close(OH);

exit 0;

# sitgroup_get_sits calculates the sum of all situations which are in this group or
# further groups in the DAG [Directed Acyclic Graph] that composes the
# situation groups. Result is returned in the global hash sum_sits which the caller manages.

# $grp_grp is an array
# $grp_grp[$base_node] is one scalar instance
# The instance is actually a hash of values, so we reference that by forcing it
#   %{$grp_grp[$base_node]} and that way the hash can be worked on.

sub sitgroup_get_sits
{
   my $base_node = shift;     # input index

   while( my ($refsit, $refval) = each %{$grp_sit[$base_node]}) {    # capture the situations into global hash.
      $sum_sits{$refsit} = 1;
      logit(100,"Sitgroup $refsit added from $grp[$base_node]");
   }
   while( my ($refgrp, $refval) = each %{$grp_grp[$base_node]}) {    # for groups, call recursively
      my $refgx = $grpx{$refgrp};
      next if !defined $refgx;
      logit(100,"Sitgroup seach entering $grp[$refgx] from $grp[$base_node]");
      sitgroup_get_sits($refgx);
   }
}

# following routine collects a list of unique attribute groups
# will be used in future report segments

sub check_table {
   (my $group) = @_;
   return if substr($group,0,1) eq "*";   # ignore tests against history table
   ${$sit_alltables[$curi]}{$group} = 1;            # add to alltables hash
#  return if substr($group,0,10) eq "Local_Time";   # ignore tests against history table
#  return if substr($group,0,14) eq "Universal_Time";   # ignore tests against history table
   $key = " " . $group . " ";
   my $ndx = index($sit_tables[$curi],$key);
   $sit_tables[$curi] .= $key if $ndx == -1;
   $ndx = index(" Process Linux_Process KLZ_Process NT_Process NT_Process_64 ",$key);
   $sit_process[$curi] = 1 if $ndx != -1;
   $ndx = index(" File_Information Linux_File_Information NT_FILE_TREND ",$key);
   $sit_fileinfo[$curi] = 1 if $ndx != -1;
   $ndx = index(" File_Information Linux_File_Information NT_FILE_TREND ",$key);
   $sit_fileinfo[$curi] = 1 if $ndx != -1;
}

# following routines are involved during the Marpa parse.

sub My_Actions::do_condition {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    print "My_Actions::do_condition: 2[$pt2]\n" if $opt_v == 1;
    $sit_and[$curi] += 1 if $$t2[0] eq "*AND";
    $sit_or[$curi] += 1 if $$t2[0] eq "*OR";
    return undef;
}

sub My_Actions::do_histrule_where {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    print "My_Actions::do_value: 1[$pt1] 2[$pt2]\n" if $opt_v == 1;
    push(@{$sit_noprivate[$curi]},"*HISTRULE");
    push(@{$sit_noprivate_FP4[$curi]},"*HISTRULE");
    push(@{$sit_noprivate_V8[$curi]},"*HISTRULE");
    push(@{$sit_function[$curi]},"*HISTRULE");
    $pt2 =~ /\"HISTORY\",\"(.*?)\"/;
    return undef if ! defined $1;
    $sit_history_collect[$curi] = $1;
    $pt2 =~ /\"INTERVAL\",\"(.*?)\"/;
    return undef if ! defined $1;
    $sit_history_interval[$curi] = ($1 + 0)/1000;
    $pt2 =~ /\"WAREHOUSE\",\"TRIGGER\((\d+)\)\"/;
    return undef if ! defined $1;
    $sit_history_export[$curi] = $1 * $sit_history_interval[$curi];
    return undef;
}


sub My_Actions::do_value {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    check_table($$t2[0]);
    push(@{$sit_function[$curi]},"*VALUE");
    print "My_Actions::do_value: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
    my $attrgroup = $$t2[0];
    my $attr = $$t2[2];
    if ($attrgroup eq "ManagedSystem") {
       if ($attr eq "Status") {
          if ($$t3[0] eq "*EQ"){
             if (($$t4[0] eq "*OFFLINE") or ($$t4[0] eq "'*OFFLINE'")) {
                $sit_ms_offline[$curi] += 1;
             } elsif (($$t4[0] eq "*ONLINE") or ($$t4[0] eq "'*ONLINE'")) {
                $sit_ms_online[$curi] += 1;
             }
          } else {
             if (($$t4[0] eq "*OFFLINE") or ($$t4[0] eq "'*OFFLINE'")) {
                $sit_ms_online[$curi] += 1;
             } elsif (($$t4[0] eq "*ONLINE") or ($$t4[0] eq "'*ONLINE'")) {
                $sit_ms_offline[$curi] += 1;
             }
          }
       } elsif ($attr eq "Reason") {
         if ($$t3[0] eq "*NE"){
            if (($$t4[0] eq "FA") or ($$t4[0] eq "'FA'")) {
               $sit_reason_ne_fa[$curi] += 1;
            }
         }
       }
    }
    if (defined $attr) {
       if (substr($attr,-2,2) eq "_U") {
          $sit_utfwild[$curi] += 1 if index($$t4[0],"*") != -1;
       }
       my $atrkey = $attrgroup . "." . $attr;
       my $atrlen = $atrlenh{$atrkey};
       if (defined $atrlen) {
          my $atrtest = $$t4[0];
          if (substr($$t4[0],0,1) eq "'") {
             $atrtest =~ /\'(.*?)\'/;
             $atrtest = $1;
          }
          if (defined $atrtest) {
             $sit_atrlen[$curi] += 1 if length($atrtest) != $atrlen;
          }
       }
       $sit_attribs[$siti]{$atrkey} += 1;
    }
    $sit_ProcessFilter[$curi] += 1 if $pt2 eq "Process . ProcessFilter_U";
    $sit_ProcessFilter[$curi] += 1 if $pt2 eq "KLZ_Process . Process_Filter";
    $sit_fileinfo_path[$curi] += 1 if $pt2 eq "Fileinfo . Path";
    $sit_fileinfo_file[$curi] += 1 if $pt2 eq "Fileinfo . File";
    $sit_fileinfo_path[$curi] += 1 if $pt2 eq "Linux_File_Information . Path_U";
    $sit_fileinfo_file[$curi] += 1 if $pt2 eq "Linux_File_Information . File_Name_U";
    $sit_fileinfo_path[$curi] += 1 if $pt2 eq "NT_FILE_TREND . Watch_Directory";
    $sit_fileinfo_file[$curi] += 1 if $pt2 eq "NT_FILE_TREND . Watch_File";
    $sit_fileinfo_path[$curi] += 1 if $pt2 eq "NT_FILE_TREND . Watch_Directory_U";
    $sit_fileinfo_file[$curi] += 1 if $pt2 eq "NT_FILE_TREND . Watch_File_U";
    $sit_nteventlog_eventid[$curi] += 1 if $pt2 eq "NT_Event_Log . Event_ID";
    $sit_nteventlog_logname[$curi] += 1 if $pt2 eq "NT_Event_Log . Log_Name";
    $sit_nteventlog_logname[$curi] += 1 if $pt2 eq "NT_Event_Log . Log_Name_U";
    $sit_correlated[$curi] += 1 if $pt2 eq "*HSITNAME";
    if ($pt3 eq "*GE") {
#      print STDERR "Working on $sit[$curi]\n";
       my $testval = $pt4;
       if (substr($pt4,0,1) eq "'") {
          $testval =~ m/\'(.*?)\'/;
          $testval = $1 if defined $1;
       }
       $testval =~ m/([0-9\.]+)/;
       if (defined $1) {
          if ($1 eq $testval){
             $testval =~ s/\.//g;
             $testval = 0 + $testval;
             if (($attrgroup ne "Local_Time") and ($attrgroup ne "Universal_Time")) {
                $sit_alwaystrue[$curi] += 1 if $testval == 0;
             }
          }
       }
    }
    return undef;
}

sub My_Actions::do_count {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    check_table($$t2[0]);
    push(@{$sit_noprivate[$curi]},"*COUNT");
    push(@{$sit_function[$curi]},"*COUNT");
    print "My_Actions::do_count 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
    $sit_count[$curi] += 1;
    if (($pt4 eq "0") or ($pt4 eq "'0'")) {
       $sit_count_zero[$curi] += 1;
    } elsif (($pt3 eq "*LT") or ($pt3 eq "*LE")) {
       if (($pt4 eq "1") or ($pt4 eq "'1'")) {
          $sit_count_ltone[$curi] += 1;
       } else {
          $sit_count_lt[$curi] += 1;
       }
    }
    $sit_count_attr[$curi]{$pt2} = 1;
    if (($pt2 eq "KLZ_Process . Process_Count") or ($pt2 eq "Linux_Process . Process_Count") or ($pt2 eq "Process . Process_Count")) {
       $sit_count_process[$curi] += 1;
    }
    return undef;
}

sub My_Actions::do_value_in {
    my ( undef, $t1, $t2, $t3, $t4, $t5, $t6) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    my @tt5 = get_list($t5);
    $sit_inct[$curi] += $#tt5/2 + 1;
    my $pt5 = join("",@tt5);
    my $pt6 = $t6; $pt6 = join(" ",@{$t6}) if ref($t4) eq 'ARRAY';
    $sit_in[$curi] += 1;
    check_table($$t2[0]);
    if (substr($$t2[2],-2,2) eq "_U") {
       $sit_utfwild[$curi] += 1 if index($pt5,"*") != -1;
    }
    push(@{$sit_noprivate[$curi]},"*IN");
    push(@{$sit_noprivate_FP4[$curi]},"*IN");
    # EPIC handles *IN
    #push(@{$sit_noprivate_V8[$curi]},"*IN");
    push(@{$sit_function[$curi]},"*IN");
    push(@{$sit_function[$curi]},"*VALUE");
    print "My_Actions::do_value_in[$pt1] 2[$pt2] 3[$pt3] 4[$pt4] 5[$pt5] 6[$pt6]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_scalar {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    if ($pt1 eq "*AVG") {
      $sit_avg[$curi] += 1;
    } elsif ($pt1 eq "*SUM") {
      $sit_sum[$curi] += 1;
    } elsif ($pt1 eq "*CHANGE") {
      $sit_change[$curi] += 1;
    } elsif ($pt1 eq "*PCTCHANGE") {
      $sit_pctchange[$curi] += 1;
    } else {
       warn "Unknown scalar action $pt1\n";
    }
    check_table($$t2[0]);
    push(@{$sit_noprivate[$curi]},$pt1);
    push(@{$sit_noprivate_FP4[$curi]},$pt1);
    # EPIC handles *AVG/*SUM/*CHANGE/*PCTCHANGE
    #push(@{$sit_noprivate_V8[$curi]},$pt1);
    push(@{$sit_function[$curi]},"$pt1");
    print "My_Actions::do_scalar: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
                return undef;
}

sub My_Actions::do_time {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    $sit_time[$curi] += 1;
    if (substr($pt4,0,1) eq "'") {
       $pt4 =~ /'(.*)\./;
       my $time_test_attribute = $1;
       if ($time_test_attribute eq $$t2[0]) {
          $sit_time_same[$curi] += 1;
          push(@{$sit_noprivate[$curi]},"InvalidTime");
          push(@{$sit_noprivate_FP4[$curi]},"InvalidTime");
          push(@{$sit_noprivate_V8[$curi]},"InvalidTime");
       }
    }
    if (($pt3 eq "*EQ") or ($pt3 eq "*NE")){
       $sit_timeneeq[$curi] += 1;
    }
    if (substr($pt4,0,1) eq "'") {
       $pt4 =~ /Time.Timestamp (.)/;
       my $subplus = $1;
       if (defined $subplus) {
          if ($subplus eq "+") {
             $sit_timefuture[$curi] += 1 if substr($pt3,0,2) eq "*L";
          } elsif ($subplus eq "-") {
             $sit_timefuture[$curi] += 1 if substr($pt3,0,2) eq "*G";
          }
       }
    }
    push(@{$sit_noprivate[$curi]},"*TIME");
#   push(@{$sit_noprivate_FP4[$curi]},"*TIME");
#   push(@{$sit_noprivate_V8[$curi]},"*TIME");
    push(@{$sit_function[$curi]},"*TIME");
    check_table($$t2[0]);
    print "My_Actions::do_time: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
                return undef;
}

sub My_Actions::do_minmax {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    if ($pt1 eq "*MIN") {
      $sit_min[$curi] += 1;
    } elsif ($pt1 eq "*MAX") {
      $sit_max[$curi] += 1;
    } else {
       warn "Unknown minmax action $pt1\n";
    }
    check_table($$t2[0]);
    push(@{$sit_noprivate[$curi]},$pt1);
    push(@{$sit_noprivate_FP4[$curi]},$pt1);
    # EPIC handles *MIN/MAX
    #push(@{$sit_noprivate_V8[$curi]},$pt1);
    push(@{$sit_function[$curi]},"$pt1");
    print "My_Actions::do_minmax: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_missing {
    my ( undef, $t1, $t2, $t3, $t4, $t5, $t6) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    my @pt5l = get_list($t5);
    my $pt5 = join("",get_list($t5));
    my $pt6 = $t6; $pt6 = join(" ",@{$t6}) if ref($t6) eq 'ARRAY';
    $sit_missing_ct[$curi] = ($#pt5l+2)/2;
    $sit_missing[$curi] += 1;
    check_table($$t2[0]);
    if (substr($$t2[2],-2,2) eq "_U") {
       $sit_utfwild[$curi] += 1 if index($pt5,"*") != -1;
    }
    push(@{$sit_function[$curi]},"*MISSING");
    print "My_Actions::do_missing: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4] 5[$pt5] 6[$pt6]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_scan {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    $sit_scan[$curi] += 1;
    check_table($$t2[0]);
    if ($pt3 eq "*NE") {
       my $testval = $pt4;
       if (substr($pt4,0,1) eq "'") {
          $testval =~ m/\'(.*?)\'/;
          $testval = $1 if defined $1;
       }
       $sit_scan_ne[$curi] += 1;
    }
    # *SCAN can be implemented using *REGEX

    push(@{$sit_workprivate[$curi]},"*SCAN");
    push(@{$sit_workprivate_FP4[$curi]},"*SCAN");

    # EPIC handles *SCAN
#   push(@{$sit_workprivate_V8[$curi]},"*SCAN");
    push(@{$sit_function[$curi]},"*SCAN");
    print "My_Actions::do_scan_quoted: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
    return undef;
}


sub My_Actions::do_str {
    my ( undef, $t1, $t2, $t3, $t4, $t5, $t6 ) = @_;
    $t5 = "" if !defined $t5;
    $t6 = "" if !defined $t6;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    my $pt5 = $t5; $pt4 = join(" ",@{$t5}) if ref($t5) eq 'ARRAY';
    my $pt6 = $t6; $pt4 = join(" ",@{$t6}) if ref($t6) eq 'ARRAY';
    $sit_str[$curi] += 1;
    check_table($$t2[0]);
    push(@{$sit_workprivate[$curi]},"*STR");
    push(@{$sit_workprivate_FP4[$curi]},"*STR");
    # EPIC handles *STR
    #push(@{$sit_workprivate_V8[$curi]},"*STR");
    push(@{$sit_function[$curi]},"*STR");
    print "My_Actions::do_str: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4] 5[$pt5] 6[$pt6]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_sit {
    my ( undef, $t1, $t2, $t3, $t4 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    $sit_sit[$curi] += 1;
    ${$sit_sits[$curi]}{$pt2} = 1;            # add to sit_sits hash
    push(@{$sit_noprivate[$curi]},"*SIT");
    push(@{$sit_noprivate_FP4[$curi]},"*SIT");
    push(@{$sit_noprivate_V8[$curi]},"*SIT");
    push(@{$sit_function[$curi]},"*SIT");
    print "My_Actions::do_sit: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_until_sit {
    my ( undef, $t1, $t2 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    $sit_until_sit[$curi] = $pt2;
    push(@{$sit_noprivate[$curi]},"*UNTIL*SIT");
    push(@{$sit_noprivate_FP4[$curi]},"*UNTIL*SIT");
    push(@{$sit_noprivate_V8[$curi]},"*UNTIL*SIT");
    push(@{$sit_function[$curi]},"*UNTIL*SIT");
    print "My_Actions::do_until_sit: 1[$pt1] 2[$pt2]\n " if $opt_v == 1;
    return undef;
}

sub My_Actions::do_until_ttl {
    my ( undef, $t1, $t2, ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    $sit_until_ttl[$curi] = $pt2;
    push(@{$sit_function[$curi]},"*UNTIL*TTL");
    print "My_Actions::do_until_sit: 1[$pt1] 2[$pt2]\n" if $opt_v == 1;
    return undef;
}

sub My_Actions::do_until_sit_ttl {
    my ( undef, $t1, $t2, $t3, $t4, $t5 ) = @_;
    my $pt1 = $t1; $pt1 = join(" ",@{$t1}) if ref($t1) eq 'ARRAY';
    my $pt2 = $t2; $pt2 = join(" ",@{$t2}) if ref($t2) eq 'ARRAY';
    my $pt3 = $t3; $pt3 = join(" ",@{$t3}) if ref($t3) eq 'ARRAY';
    my $pt4 = $t4; $pt4 = join(" ",@{$t4}) if ref($t4) eq 'ARRAY';
    my $pt5 = $t5; $pt5 = join(" ",@{$t5}) if ref($t5) eq 'ARRAY';
    $sit_until_sit[$curi] = $pt2;
    $sit_until_ttl[$curi] = $pt5;
    push(@{$sit_noprivate[$curi]},"*UNTIL*SIT");
    push(@{$sit_noprivate_FP4[$curi]},"*UNTIL*SIT");
    push(@{$sit_noprivate_V8[$curi]},"*UNTIL*SIT");
    push(@{$sit_function[$curi]},"*UNTIL*TTL*SIT");
    print "My_Actions::do_until_sit: 1[$pt1] 2[$pt2] 3[$pt3] 4[$pt4] 5[$pt5]\n" if $opt_v == 1;
    return undef;
}

# routine to unwind a mixed array with multiple depths

sub get_list {
    my @work = @_;
    my @result;
    while (@work) {
        my $next = shift @work;
        if (ref($next) eq 'ARRAY') {
            unshift @work, @$next;
        }
        else {
            push @result, $next;
        }
    }
    return @result;
}

# Detect attribute groups in situations based on *SIT True test
# As part of logic also detect cycles in *SIT usages. Situations created in
# TEP Situation editor will not allow such conditions be it could be created
# by directly changed formula using tacmd editSit or direct SQL.
#
# Inspired by this Depth-First Search article:
# http://www.personal.kent.edu/~rmuhamma/Algorithms/MyAlgorithms/GraphAlgor/depthSearch.htm
# However the logic bears no relationship to the reference algorithms

# Analyze top level situations

sub cycle_sit {
  my $cx = shift;
  $sittopi = $cx;
  my $vx;
  $sitcyclerc = 0;
  %sitcyclex = ();                     # clear out working hash
  @sitcycle = ();                      # clear out working array
  my $sitone = $sit[$cx];
  if (!defined $sitone) {               # unknown situation is tracked elsewhere, ignore here
     $sitcyclerc = -1;
  } else {
#print "cycle_sit $cx $sitone\n";
     push (@sitcycle,$sitone);          # At starting point, no possible conflict first in array
     $sitcyclex{$sitone} = 1;           # and present in situation usage hash
     foreach my $g (keys %{$sit_sits[$cx]}) {
        $vx = $sitx{$g};
        next if !defined $vx;              # unknown situation but will show in advisory elsewhere
        $rc = cycle_visit_sit($vx);
        last if $sitcyclerc != 0;
     }
     if ($sitcyclerc > 0) {
          my $loopsit = join(":",@sitcycle);
          $advi++;$advonline[$advi] = "Situation with looping *SIT evaluations [$loopsit]";
          $advcode[$advi] = "SITAUDIT1049E";
          $advimpact[$advi] = $advcx{$advcode[$advi]};
          $advsit[$advi] = $sit_psit[$sittopi];
     }
  }
}

# Recursive entry to *SIT analysis

sub cycle_visit_sit {
   if ( $sitcyclerc > 0) {
      return $sitcyclerc;
   }
#   return $sitcyclerc if $sitcyclerc > 0;
   $gx = shift;
   my $sitone = $sit[$gx];
   if (defined $sitone) {
#print "cycle_visit_sit $gx $sitone\n";
      if (defined $sitcyclex{$sitone}) {     # if found a loop,
        push (@sitcycle,$sitone);           # looping situation at end of usage array
        $sitcyclerc = 1;                    #   trigger bailout with @sitcycle intact
        return $sitcyclerc;
      } else {
         # for the tables in the reference situation, add to the base situation tables
         # even if a looping failure follows, the alltables will be more correct and thus eliminate some false positives
         foreach my $a (keys %{$sit_alltables[$gx]}) {
            $sit_alltables[$sittopi]{$a} = 1;               # always add, if already exist things don't change
         }
         push (@sitcycle,$sitone);          # Add new situation at end of usage array
         $sitcyclex{$sitone} = 1;           # add to situation usage hash
         foreach my $g (keys %{$sit_sits[$gx]}) {             # for each v adjacent to u
            my $vx = $sitx{$g};
            next if !defined $vx;
            $rc = cycle_visit_sit($vx);
            return if $sitcyclerc > 0;
         }
         pop (@sitcycle);                   #delete end of usage element
         delete $sitcyclex{$sitone};        #remove hash
      }
   }
}

sub newsit {
      my ($isitname,$ipdt,$ifullname,$iautostart,$isitinfo,$icmd,$iautosopt,$ireev_days,$ireev_time,$ilstdate,$iaffinities) = @_;
      $siti += 1;
      $sit[$siti] = $isitname;
      $sit_psit[$siti] = $isitname;
      $sitx{$isitname} = $siti;
      $sit_pdt[$siti] = $ipdt;
      $sit_fullname[$siti] = $ifullname;
      $sit_autostart[$siti] = $iautostart;
      $sit_autosopt[$siti] = $iautosopt;
      $sit_lstdate[$siti] = $ilstdate;
      $sit_aff_agent[$siti] = substr("$iaffinities   ",0,32);
      $sit_atrlen[$siti] = 0;
      $sit_attribs[$siti] = {};
      $sit_domain_pass[$siti] = 0;
      $sit_correlated[$siti] = 0;
      $sit_timeneeq[$siti] = 0;
      $sit_timefuture[$siti] = 0;
      $sit_reeval_bad_days[$siti] = 0;
      if ((length($ireev_days) < 1) or (length($ireev_days) > 3) ) {
         $sit_reeval_bad_days[$siti] = 1;
      }
      if (length($isitname) == 32) {
         $advi++;$advonline[$advi] = "SITNAME is 32 bytes long - illegal and will be usually ignored - fullname [$ifullname]";
         $advcode[$advi] = "SITAUDIT1060W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $sit[$siti];
      }
      $sit_reeval_bad_time[$siti] = 0;
      $sit_reeval_bad_time[$siti] = 1 if length($ireev_time) > 6;
      $ireev_days += 0;
      my $reev_time_hh = 0;
      my $reev_time_mm = 0;
      my $reev_time_ss = 0;
      if ($ireev_time ne "0") {
         $reev_time_hh = substr($ireev_time,0,2);
         $reev_time_mm = substr($ireev_time,2,2);
         $reev_time_ss = substr($ireev_time,4,2);
      }
      $sit_reeval[$siti] = $ireev_days*86400 + $reev_time_hh*3600 + $reev_time_mm*60 + $reev_time_ss;   # sampling interval in seconds

      $sit_sitinfo[$siti] = $isitinfo;
      $sit_persist[$siti] = 1;                      # persist count = 1 if not present
      if (index($sit_sitinfo[$siti],"COUNT=") != -1) {
         $sit_sitinfo[$siti] =~ /COUNT=(\d+)/;
         $sit_persist[$siti] = $1 if defined $1;
      }
      $sit_dst[$siti] = "";                                 # Assume no event destinations
      if (index($sit_sitinfo[$siti],"TDST=") != -1) {
         $sit_sitinfo[$siti] =~ /TDST=([,\d]+)/;
         $sit_dst[$siti] = $1 if defined $1;
      }
      $sit_atom[$siti] = "";                                 # Assume no atomize
      if (index($sit_sitinfo[$siti],"ATOM=") != -1) {
         if ((index($sit_sitinfo[$siti],"ATOM=;") == -1) and (index($sit_sitinfo[$siti],"ATOM='';") == -1)) {
            $sit_sitinfo[$siti] =~ /ATOM=(.*?)[;~]/;
            if (defined $1) {
               $sit_atom[$siti] = $1;
            } else {
               $sit_sitinfo[$siti] =~ /ATOM=(.*?)$/;
               $sit_atom[$siti] = $1  if defined $1;
            }
         }
      }
      $sit_multi[$siti] = 0;                                # Assume no multi-row
      $sit_ProcessFilter[$siti] = 0;                        # assume no Process Filter
      $sit_alwaystrue[$siti] = 0;                           # assume no value always true
      $sit_cmd[$siti] = 1;                                  # Assume CMD is present = 1
      $sit_cmd[$siti] = 0 if substr($icmd,0,5) eq "*NONE";  # else 0
      $sit_cmdtext[$siti] = $icmd;
      $sit_value[$siti] = 0;
      $sit_sit[$siti] = 0;
      $sit_str[$siti] = 0;
      $sit_scan[$siti] = 0;
      $sit_scan_ne[$siti] = 0;
      $sit_change[$siti] = 0;
      $sit_in[$siti] = 0;
      $sit_inct[$siti] = 0;
      $sit_pctchange[$siti] = 0;
      $sit_count[$siti] = 0;
      $sit_count_zero [$siti] = 0;
      $sit_count_ltone[$siti] = 0;
      $sit_count_lt[$siti] = 0;
      $sit_count_process[$siti] = 0;
      $sit_count_attr[$siti] = ();                   # has of *COUNT attributes
      $sit_min[$siti] = 0;
      $sit_max[$siti] = 0;
      $sit_avg[$siti] = 0;
      $sit_sum[$siti] = 0;
      $sit_time[$siti] = 0;
      $sit_time_same[$siti] = 0;
      $sit_and[$siti] = 0;
      $sit_or[$siti] = 0;
      $sit_noprivate[$siti] = [];                   # array of reasons why private sits are invalid
      $sit_noprivate_FP4[$siti] = [];               # array of reasons why private sits are invalid ITM 630 FP4
      $sit_noprivate_V8[$siti] = [];                # array of reasons why private sits are invalid V8
      $sit_workprivate[$siti] = [];                 # array of reasons why private sits need work
      $sit_workprivate_FP4[$siti] = [];             # array of reasons why private sits need work ITM 630 FP4
      $sit_workprivate_V8[$siti] = [];              # array of reasons why private sits need work V8
      $sit_function[$siti] = [];                    # array of functions used
      $sit_until_ttl[$siti] = "";
      $sit_until_sit[$siti] = "";
      $sit_tables[$siti] = "";                      # tables less time attribute group
      $sit_alltables[$siti] = {};                   # all attribute goups, hash reference
      $sit_missing[$siti] = 0;                      # count of *MISSING
      $sit_missing_ct[$siti] = 0;                   # count of *MISSING comparands
      $sit_ms_offline[$siti] = 0;                   # count of MS_Offline type tests
      $sit_ms_online[$siti] = 0;                    # count of MS_Online type tests
      $sit_reason_ne_fa[$siti] = 0;                 # count of MS_Online Reason ne FA type tests
      $sit_syntax[$siti] = 0;                       # syntax error
      $sit_filter[$siti] = "";                      # Where filtered
      $sit_dist[$siti] = 0;                         # When 1, there is a distribution
      $sit_dist_objaccl[$siti] = "";                # list of distributions
      $sit_process[$siti] = 0;                      # Attributes related to Process
      $sit_utfwild[$siti] = 0;                      # Unicode attribute with wildcard test
      $sit_fileinfo[$siti] = 0;                     # Attributes related to FileInfo
      $sit_fileinfo_path[$siti] = 0;                # Attributes related to FileInfo w/Path
      $sit_fileinfo_file[$siti] = 0;                # Attributes related to FileInfo w/File
      $sit_nteventlog_eventid[$siti] = 0;           # Attributes related to NT_Event_Log/Event_ID
      $sit_nteventlog_logname[$siti] = 0;           # Attributes related to NT_Event_log/Log_Name
      $sit_history_collect[$siti] = "";             # Where STH files collected
      $sit_history_interval[$siti] = 0;             # If History collection file, how often collected in seconds
      $sit_history_export[$siti]  = 0;              # If History collection file, how many collections before export
      $sit_subset[$siti] = ();                      # array of substr names
      my $pdt_ref = $pdtx{$ipdt};                   # collect has if pdt usages
      if (!defined $pdt_ref) {
         my %pdtref = (
                        count => 0,
                        sits => [],
                      );
         $pdt_ref = \%pdtref;
         $pdtx{$ipdt} = \%pdtref;
      }
      $pdt_ref->{count} += 1;
      push (@{$pdt_ref->{sits}},$sit[$siti]);
}

# Parse for KfwSQLClient SQL capture

sub parse_lst {
  my ($lcount,$inline,$cref) = @_;      # count of desired chunks and the input line
  my @retlist = ();                     # an array of strings to return
  my $chunk = "";                       # One chunk
  my $oct = 1;                          # output chunk count
  my $rest;                             # the rest of the line to process
  my $fixed;
  $inline =~ /\]\s*(.*)/;               # skip by [NNN]  field
  $rest = " " . $1 . "        ";
  my $lenrest = length($rest);          # length of $rest string
  my $restpos = 0;                      # postion studied in the $rest string
  my $nextpos = 0;                      # floating next position in $rest string

  # KwfSQLClient logic wraps each column with a leading and trailing blank
  # simple case:  <blank>data<blank><blank>data1<blank>
  # data with embedded blank: <blank>data<blank>data<blank><data1>data1<blank>
  #     every separator is always at least two blanks, so a single blank is always embedded
  # data with trailing blank: <blank>data<blank><blank><blank>data1<blank>
  #     given the rules has to be leading or trailing blank and chose trailing on data
  # data followed by a null data item: <blank>data<blank><blank><blank><blank>
  #                                                            ||
  # data with longer then two blanks embedded must be placed on end, or handled with a cref hash.
  #
  # $restpos always points within the string, always on the blank delimiter at the end
  while ($restpos < $lenrest) {
     $fixed = $cref->{$oct};
     if (defined $fixed) {
        # working on affinities
        my $rrest = substr($rest,$restpos+1);
        my $if_ndx = index($rrest,"*IF");
        if ($if_ndx == -1) {
           $rrest .= " " x 60;
           $chunk = substr($rrest,$fixed);
           push @retlist, $chunk;                 # record null data chunk
           $restpos += 2 + $fixed;
           $chunk = "";
           $oct += 1;
           next;
        } else {
           $chunk = substr($rest,$restpos+1,$if_ndx-2);
           push @retlist, $chunk;                 # record null data chunk
           $restpos += $if_ndx;
           $chunk = "";
           $oct += 1;
           next;
        }
     }
     if ($oct >= $lcount) {                                   # handle last item
        $chunk = substr($rest,$restpos+1);
        $chunk =~ s/\s+$//;                    # strip trailing blanks
        push @retlist, $chunk;                 # record last data chunk
        last;
     }
     if ((substr($rest,$restpos,3) eq "   ") and (substr($rest,$restpos+3,1) ne " ")) {          # following null entry
        $chunk = "";
        $oct += 1;
        push @retlist, $chunk;                 # record null data chunk
        $restpos += 2;
        next;
     }
     if ((substr($rest,$restpos,2) eq "  ") and (substr($rest,$restpos+2,1) ne " ")) {            # trailing blank on previous chunk so ignore
        $restpos += 1;
        next;
     }

     $nextpos = index($rest," ",$restpos+1);
     if (substr($rest,$nextpos,2) eq "  ") {
        $chunk .= substr($rest,$restpos+1,$nextpos-$restpos-1);
        push @retlist, $chunk;                 # record null data chunk
        $chunk = "";
        $oct += 1;
        $restpos = $nextpos + 1;
     } else {
        $chunk .= substr($rest,$restpos+1,$nextpos-$restpos);
        $restpos = $nextpos;
     }
  }
  return @retlist;
}


# following routine gets data from txt files. tems2sql.pl is an internal only program which can
# extract data from a TEMS database file.

#perl \rexx\bin\tems2sql.pl -txt -s SITNAME -tlim 0 -tc SITNAME,AUTOSTART,SITINFO,CMD,AUTOSOPT,REEV_DAYS,REEV_TIME,PDT  c:\ibm\itm622\kib.cat  QA1CSITF.DB  > QA1CSITF.DB.TXT
#perl \rexx\bin\tems2sql.pl -txt -s ID -tc ID,FULLNAME  c:\ibm\itm622\kib.cat  QA1DNAME.DB  > QA1DNAME.DB.TXT

sub init_all {
   my @kgrp_data;
   my @kgrpi_data;
   my @ksit_data;
   my @ktna_data;
   my @klst_data;
   my @ksav_data;
   my @kobj_data;
   my @kevp_data;
   my @kact_data;
   my @kovr_data;
   my $isitname;
   my $ifullname;
   my $ipdt;
   my $iautostart;
   my $isitinfo;
   my $icmd;
   my $iautosopt;
   my $ireev_days;
   my $ireev_time;
   my $ilstdate;
   my $iid;
   my $igrpclass;
   my $iobjname;
   my $iobjclass;
   my $inodel;
   my $inodetype;
   my $itypestr;
   my $iactinfo;
   my $read_fn;
   my $ilnode;
   my $ilnodelist;
   my $iproduct;
   my $io4offline;
   my $iaffinities;
   my $inode;

   $read_fn = $opt_txt_tgroup if $opt_txt == 1;
   $read_fn = $opt_lst_tgroup if $opt_lst == 1;

   open(KGRP, "< $read_fn") || die("Could not open TGROUP $read_fn\n");
   @kgrp_data = <KGRP>;
   close(KGRP);

   # make an array of all group identifications
   $ll = 0;
   foreach $oneline (@kgrp_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $iid = substr($oneline,0,32);
         $iid =~ s/\s+$//;   #trim trailing whitespace
         $igrpclass = substr($oneline,33,4);
      } else {
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT ID,GRPCLASS FROM O4SRV.TGROUP" >QA1DGRPA.DB.LST
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         ($iid,$igrpclass) = parse_lst(2,$oneline);
      }
      next if $igrpclass ne '2010';
      $gx = $grpx{$iid};
      if (!defined $gx) {
         $grpi++;
         $gx = $grpi;
         $grp[$gx] = $iid;
         $grpx{$iid} = $gx;
         $grp_sit[$gx] = {};
         $grp_grp[$gx] = {};
      }
   }

   $read_fn = $opt_txt_tgroupi if $opt_txt == 1;
   $read_fn = $opt_lst_tgroupi if $opt_lst == 1;

   open(KGRPI, "< $read_fn") || die("Could not open TGROUPI $read_fn\n");
   @kgrpi_data = <KGRPI>;
   close(KGRPI);

   # Work through all the group items
   $ll = 0;
   foreach $oneline (@kgrpi_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $iid = substr($oneline,0,32);
         $iid =~ s/\s+$//;   #trim trailing whitespace
         $iobjname = substr($oneline,33,32);
         $iobjname =~ s/\s+$//;   #trim trailing whitespace
         $iobjclass = substr($oneline,66,4);
         $igrpclass = substr($oneline,75,4);
      } else {
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT ID,OBJNAME,OBJCLASS FROM O4SRV.TGROUP" >QA1DGRPI.DB.LST
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         ($iid,$iobjname,$iobjclass) = parse_lst(3,$oneline);
      }
      next if $igrpclass ne '2010';
      if (($iobjclass ne '5140') & ($iobjclass ne '2010')) {
         next;
      }
      $gx = $grpx{$iid};
      if (!defined $gx) {
         warn "unknown group id $iid.\n";
         next;
      }
      $grp_sit[$gx]->{$iobjname} = 1 if $iobjclass eq '5140';
      $grp_grp[$gx]->{$iobjname} = 1 if $iobjclass eq '2010';
   }

   $read_fn = $opt_txt_tsitdesc if $opt_txt == 1;
   $read_fn = $opt_lst_tsitdesc if $opt_lst == 1;

   open(KSIT, "< $read_fn") || die("Could not open TSITDESC $read_fn\n");
   @ksit_data = <KSIT>;
   close(KSIT);

   # Following extracts of data are specific to the utility used

   $ll = 0;
   foreach $oneline (@ksit_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
      }
      $oneline .= " " x 600;
      if (length($oneline) == 0) {
         $advi++;$advonline[$advi] = "Situation definition is blank";
         $advcode[$advi] = "SITAUDIT0999E";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = "*NONE";
         $impossible{$sit[$siti]} = 1;
         next;
      }
      if ($opt_txt == 1) {
         $isitname = substr($oneline,0,32);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
         $iautostart = substr($oneline,33,4);
         $iautostart =~ s/\s+$//;   #trim trailing whitespace
         $isitinfo = substr($oneline,38,128);
         $isitinfo =~ s/\s+$//;   #trim trailing whitespace
         $icmd = substr($oneline,167,506);
         $icmd =~ s/\s+$//;   #trim trailing whitespace
         $iautosopt = substr($oneline,676,3);
         $iautosopt =~ s/\s+$//;   #trim trailing whitespace
         $ireev_days = substr($oneline,685,3);
         $ireev_days =~ s/\s+$//;   #trim trailing whitespace
         $ireev_time = substr($oneline,689,6);
         $ireev_time =~ s/\s+$//;   #trim trailing whitespace
         $ilstdate = substr($oneline,698,16);
         $ilstdate =~ s/\s+$//;   #trim trailing whitespace
         $iaffinities = substr($oneline,715,43);
         $iaffinities =~ s/\s+$//;   #trim trailing whitespace
         $ipdt = "";
         if (length($oneline) > 760) {
            $ipdt = substr($oneline,760,1020);
            $ipdt =~ s/\s+$//;   #trim trailing whitespace
         }
      } else {
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT SITNAME,AUTOSTART,SITINFO,AUTOSOPT,REEV_DAYS,REEV_TIME,LSTDATE,PDT, FROM O4SRV.TSITDESC" >QA1CSITF.DB.LST
         my %cref = (8=>43,);
         ($isitname,$iautostart,$isitinfo,$iautosopt,$ireev_days,$ireev_time,$ilstdate,$iaffinities,$ipdt) = parse_lst(9,$oneline,\%cref);
         $icmd = "";
      }
      if (length($isitname) > 31) {
         $advi++;$advonline[$advi] = "Situation name is greater then 31 characters";
         $advcode[$advi] = "SITAUDIT1045W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $isitname;
      }

      # Usually ignore autostart = *NO. However if it is a SP2OS-ish UADVISOR,
      # the situation could have been auto-distributed and so report it.
      # also work on if -runall is specified.
      $sit_tems_alert = 1 if $isitname eq "TEMS_Alert";
      if ($iautostart eq "*NO") {
         if (!defined $hSP2OS{$isitname}) {
            next if $opt_runall == 0;
         }
      }
      $sit_tems_alert_run = 1 if (($isitname eq "TEMS_Alert") and ($iautostart eq "*NO"));
      newsit($isitname,$ipdt,"",$iautostart,$isitinfo,$icmd,$iautosopt,$ireev_days,$ireev_time,$ilstdate,$iaffinities);
   }

   if ($opt_lst == 1) {
      $read_fn = $opt_lst_tsitdesc1 if $opt_lst == 1;

      open(KSIT1, "< $read_fn") || die("Could not open TSITDESC_1 $read_fn\n");
      @ksit_data = <KSIT1>;
      close(KSIT1);

      # Following extracts of data are specific to the utility used

      $ll = 0;
      foreach $oneline (@ksit_data) {
         $ll += 1;
         chop $oneline;
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT SITNAME,CMD FROM O4SRV.TSITDESC" >QA1CSITF1.DB.LST
         ($isitname,$icmd) = parse_lst(2,$oneline);
         my $sx = $sitx{$isitname};
         next if !defined $sx;
         $sit_cmd[$sx] = 1 if substr($icmd,0,5) ne "*NONE";  # command present
         $sit_cmdtext[$sx] = $icmd;
      }
   }

   # The TNAME table extract. The result is folded into @sit_fullname array.

   $read_fn = $opt_txt_tname if $opt_txt == 1;
   $read_fn = $opt_lst_tname if $opt_lst == 1;

   open(KTNA, "< $read_fn") || die("Could not open TNAME $read_fn\n");
   @ktna_data = <KTNA>;
   close(KTNA);

   $ll = 0;
   foreach $oneline (@ktna_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $iid = substr($oneline,0,32);
         $iid =~ s/\s+$//;   #trim trailing whitespace
         $ifullname = substr($oneline,33,256);
         $ifullname =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT ID,FULLNAME FROM O4SRV.TNAME" >QA1DNAME.DB.LST
         ($iid,$ifullname) = parse_lst(2,$oneline);
      }
      $sx = $sitx{$iid};
      next if !defined $sx;
      $sit_fullname[$sx] = $ifullname;
   }

   # The TNODELST table extract. The result is folded stored in %nodl hash.

   $read_fn = $opt_txt_tnodelst if $opt_txt == 1;
   $read_fn = $opt_lst_tnodelst if $opt_lst == 1;

   open(KLST, "< $read_fn") || die("Could not open TNODELST $read_fn\n");
   @klst_data = <KLST>;
   close(KLST);

   $ll = 0;
   foreach $oneline (@klst_data) {
      $ll += 1;
      chop $oneline;
      $oneline .= " " x 600;
      if ($opt_txt == 1) {
         next if $ll < 5;
         next if substr($oneline,0,1) ne "M";
         $ilnode = substr($oneline,9,32);
         $ilnode =~ s/\s+$//;   #trim trailing whitespace
         $ilnodelist = substr($oneline,42,32);
         $ilnodelist =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT NODE,NODELIST FROM O4SRV.TNODELST WHERE NODETYPE='M'" >QA1CNODL.DB.LST
         ($inodetype,$ilnode,$ilnodelist) = parse_lst(3,$oneline);
         next if $inodetype ne "M";
      }
      my $nodel_ref = $nodel{$ilnodelist};
      if (!defined $nodel_ref) {
         my %nodelref = (
                           nodes => {},
                        );
         $nodel_ref = \%nodelref;
         $nodel{$ilnodelist}  = \%nodelref;
      }
      $nodel_ref->{nodes}{$ilnode} = 1;
   }

   # The TNODESAV table extract. The result is folded stored in %nsav hash.

   $read_fn = $opt_txt_tnodesav if $opt_txt == 1;
   $read_fn = $opt_lst_tnodesav if $opt_lst == 1;

   open(KSAV, "< $read_fn") || die("Could not open TNODESAV $read_fn\n");
   @ksav_data = <KSAV>;
   close(KSAV);

   $ll = 0;
   foreach $oneline (@ksav_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $inode = substr($oneline,0,32);
         $inode =~ s/\s+$//;   #trim trailing whitespace
         $iproduct = substr($oneline,33,2);
         $iproduct =~ s/\s+$//;   #trim trailing whitespace
         $io4offline = substr($oneline,41,2);
         $io4offline =~ s/\s+$//;   #trim trailing whitespace
         $iaffinities = substr($oneline,50,43);
         $iaffinities =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT NODE,PRODUCT,O4ONLINE,AFFINITIES FROM O4SRV.TNODESAV >QA1DNSAV.DB.LST
         ($inode,$iproduct,$io4offline,$iaffinities) = parse_lst(4,$oneline);
      }
      $nsav{$inode} = $iproduct;
      my $aff_agent = substr($iaffinities,0,32);    # use the agent part of affinity to link to product code
      $nsav_aff{$aff_agent} = $iproduct;
      $nsav_online += 1 if $io4offline eq "Y";
      $nsav_offline += 1 if $io4offline eq "N";
   }

   # Third the TOBJACCL table extract.

   $read_fn = $opt_txt_tobjaccl if $opt_txt == 1;
   $read_fn = $opt_lst_tobjaccl if $opt_lst == 1;

   open(KOBJ, "< $read_fn") || die("Could not open TOBJACCL $read_fn\n");
   @kobj_data = <KOBJ>;
   close(KOBJ);

   $ll = 0;
   foreach $oneline (@kobj_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $iobjname = substr($oneline,0,32);
         $iobjname =~ s/\s+$//;   #trim trailing whitespace
         $iobjclass = substr($oneline,33,4);
         $iobjclass =~ s/\s+$//;   #trim trailing whitespace
         $inodel = substr($oneline,42,32);
         $inodel =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT OBJNAME,OBJCLASS,NODEL FROM O4SRV.TOBJACCL" >QA1DOBJA.DB.LST
         ($iobjname,$iobjclass,$inodel) = parse_lst(3,$oneline);
      }
      if ($iobjclass eq '5140') {
         $key = " OBJA." . $inodel . " ";
         $sx = $sitx{$iobjname};
         next if !defined $sx;
         $sit_tems_alert_dist = 1 if $iobjname eq "TEMS_Alert";
         $sit_dist[$sx] = 1;
         $sit_distribution = 1;
         next if index($sit_dist_objaccl[$sx],$key) != -1;
         $sit_dist_objaccl[$sx] .= $key;
      } elsif ($iobjclass eq '2010')   {
          $gx = $grpx{$iobjname};
          next if !defined $gx;
          %sum_sits = ();
          sitgroup_get_sits($gx);
          foreach my $s (keys %sum_sits) {
             $sx =  $sitx{$s};
             next if !defined $sx;
             $sit_dist[$sx] = 1;
             $sit_distribution = 1;
             $key = " GRPA." . $inodel . " ";
             next if index($sit_dist_objaccl[$sx],$key) != -1;
             $sit_dist_objaccl[$sx] .= $key;
          }
      }
   }

   $read_fn = $opt_txt_evntmap if $opt_txt == 1;
   $read_fn = $opt_lst_evntmap if $opt_lst == 1;

   open(KEVP, "< $read_fn") || die("Could not open EVNTMAP $read_fn\n");
   @kevp_data = <KEVP>;
   close(KEVP);

   # Following extracts of data are specific to the utility used

   $ll = 0;
   foreach $oneline (@kevp_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $iid = substr($oneline,0,32);
         $iid =~ s/\s+$//;   #trim trailing whitespace
         $iobjclass = substr($oneline,33,4);
         $iobjclass =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT ID,OBJCLASS FROM O4SRV.EVNTMAP" >QA1DEVMP.DB.LST
         ($iid,$iobjclass) = parse_lst(2,$oneline);
      }
      next if $iobjclass ne "2250";
      $hevmap{$iid} = 0;
   }

   $read_fn = $opt_txt_tactypcy if $opt_txt == 1;
   $read_fn = $opt_lst_tactypcy if $opt_lst == 1;

   open(KACT, "< $read_fn") || die("Could not open TACTYPCY $read_fn\n");
   @kact_data = <KACT>;
   close(KACT);

   # Following extracts of data are specific to the utility used

   $ll = 0;
   foreach $oneline (@kact_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $oneline .= " " x 300;
         $itypestr = substr($oneline,0,32);
         $itypestr =~ s/\s+$//;   #trim trailing whitespace
         $iactinfo = substr($oneline,33,252);
         $iactinfo =~  s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT TYPESTR,ACTINFO FROM O4SRV.TACTYPCY" >QA1DACTP.DB.LST
         ($itypestr,$iactinfo) = parse_lst(2,$oneline);
      }
      if (($itypestr eq "*WAIT_ON_SITUATION") or ($itypestr eq "Evaluate_Situation")) {
         $hactp{$iactinfo} = 0;
      }
   }

   $read_fn = $opt_txt_toverride if $opt_txt == 1;
   $read_fn = $opt_lst_toverride if $opt_lst == 1;

   open(KOVR, "< $read_fn") || die("Could not open TOVERRIDE $read_fn\n");
   @kovr_data = <KOVR>;
   close(KOVR);

   # Following extracts of data are specific to the utility used

   $ll = 0;
   foreach $oneline (@kovr_data) {
      $ll += 1;
      chop $oneline;
      if ($opt_txt == 1) {
         next if $ll < 5;
         $isitname = substr($oneline,0,32);
         $isitname =~ s/\s+$//;   #trim trailing whitespace
      } else {
         next if substr($oneline,0,10) eq "KCIIN0187I";      # A Linux/Unix first line
         #%CANDLE_HOME%\cnps\KfwSQLClient /e "SELECT SITNAME FROM O4SRV.TOVERRIDE" >QA1DOVRD.DB.LST
         ($isitname) = parse_lst(1,$oneline);
      }
      $hovrd{$isitname} = 0;
   }
}

# Following is the extract routine for the bulkexportsit xml files

sub init_bulk {
   use Cwd;
   use File::Find;

   # if the path is not fully specified, add the current directory.
   # In this Perl context, the forward slash alone is used for both
   # Windows and Linux/Unix
   if (index($opt_bulk_path,"/") == -1) {
      my $cwd = getcwd;
      $opt_bulk_path = $cwd . "/" . $opt_bulk_path;

   }

   # following gathers all the files in the named directory
   find(\&wanted, $opt_bulk_path);
   sub wanted {
      my $fn = $File::Find::name;
      if (-f $fn) {
         $xmli += 1;
         $xmlfile[$xmli] = $fn;
      }
   }


   # parse the xml file
   my $tpp = XML::TreePP->new();

   my $tree;
   my $isitname;
   my $ifullname;
   my $ipdt;
   my $iautostart;
   my $isitinfo;
   my $icmd;
   my $iautosopt;
   my $ireev_days;
   my $ireev_time;
   my $ilstdate;
   my $iaffinities;

   my $idist;

   for (my $i=0; $i<=$xmli; $i++) {
      $tree = $tpp->parsefile($xmlfile[$i]);
      my %row_p;
      # Some bulkexports package a second row for the event mapping object
      if (ref $tree->{TABLE}->{ROW} eq "ARRAY") {
         %row_p = %{$tree->{TABLE}->{ROW}[0]};
      } else {
         %row_p = %{$tree->{TABLE}->{ROW}};
      }

      $isitname = $row_p{SITNAME};
      if (length($isitname) > 31) {
         $advi++;$advonline[$advi] = "Situation name is greater then 31 characters";
         $advcode[$advi] = "SITAUDIT1045W";
         $advimpact[$advi] = $advcx{$advcode[$advi]};
         $advsit[$advi] = $isitname;
      }
      $sit_tems_alert = 1 if $isitname eq "TEMS_Alert";
      $iautostart = $row_p{AUTOSTART};
      if ($iautostart eq "*NO") {
         next if $opt_runall == 0;
      }
      $sit_tems_alert_run = 1 if (($isitname eq "TEMS_Alert") and ($iautostart eq "*NO"));
      $ifullname = $row_p{FULLNAME};
      $ipdt = $row_p{PDT};
      $isitinfo = $row_p{SITINFO};
      $icmd = $row_p{CMD};
      $iautosopt = $row_p{AUTOSOPT};
      $ireev_days = $row_p{REEV_DAYS};
      $ireev_time = $row_p{REEV_TIME};
      $ilstdate = $row_p{LSTDATE};
      $iaffinities = $row_p{AFFINITIES};
      $idist       = $row_p{DISTRIBUTION};
      newsit($isitname,$ipdt,$ifullname,$iautostart,$isitinfo,$icmd,$iautosopt,$ireev_days,$ireev_time,$ilstdate,$iaffinities);
      if (defined $idist) {
         if ($idist ne "") {
            $sit_dist[$siti] = 1;
            $sit_distribution = 1;
            $sit_dist_objaccl[$siti] = $idist;
            $sit_tems_alert_dist = 1 if $isitname eq "TEMS_Alert";
         }
      }
   }
}

# following extracts the data from a primary hub TEMS using SOAP
# This is derived from the Agent Health Survey logic

sub init_soap {
   use Cwd;
   use SOAP::Lite;                 # simple SOAP processing. add 'debug' to increase tracing
   use HTTP::Request::Common;      #   and HTTP - for SOAP processing

   my $tems_hub_nodeid;

   # Parse control file which contains  operational defaults -
   #

   if ($opt_vt == 1) {
      my $traffic_file = $opt_workpath . "traffic.txt";
      open $debugfile, ">$traffic_file" or die "can't open $traffic_file: $!";
      $debugfile->autoflush(1);
   }


   # SOAP Variables

   # Variables associated directly with SOAP calls and responses
   # CPU and Memory

   my $sSQL;

   # variables for storing Situation Description information from the hub TEMS

   my $sx;

   # try out each SOAP connection, looking for the current FTO hub TEMS primary
   # might be just one of course...

   my $got_connection = 0;
   my $num_connections = $#connections;

   foreach my $c (@connections) {
      #  Convert $connection as supplied by ini file into a connection string usable for soap processing
      #  That might be the string as supplied but might require changes to adapt to ports actually used
      $connection = $c;
      logit(0,"Survey trial of connection $connection");
      $rc = get_connection();
      if ($run_status) {
         logit(0,"Survey trial of connection $connection failed, continue to next");
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
   #   $oHub = SOAP::Lite->proxy($connection,timeout => $opt_soap_timeout);
   #   $oHub = SOAP::Lite->proxy($connection,keep_alive=>1,timeout => $opt_soap_timeout);
      $oHub = SOAP::Lite->proxy($connection,keep_alive=>1);
      $oHub->outputxml('true');
      $oHub->on_fault( sub {});      # pass back all errors


   $oHub->transport->add_handler( request_send => sub {
       return if $opt_vt == 0;
       my $req = shift;
       my $cur_time = time;
       print $debugfile "\n$cur_time === BEGIN HTTP REQUEST ===\n";
       print $debugfile $req->dump();
       print $debugfile "\n$cur_time ===   END HTTP REQUEST ===\n";
       return
     }
   );
   $oHub->transport->add_handler( response_header => sub {
       return if $opt_vt == 0;
       my $cur_time = time;
       my $res = shift;
       print $debugfile "\n$cur_time === BEGIN RESPONSE HDRS ===\n";
       print $debugfile $res->dump();
       print $debugfile "\n$cur_time === END RESPONSE HDRS ===\n";
       return
     }
   );
   $oHub->transport->add_handler( response_data => sub {
       my $res = shift;
       my $cur_time = time;
       if ($opt_vt == 1) {
          my $content_length = length($res->content);
          print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DATA $content_length ===\n";
          print $debugfile $res->content;
          print $debugfile "\n===   END HTTP RESPONSE DATA ===\n";
       }
   #    if (substr($res->content,-20) eq "</SOAP-ENV:Envelope>") {
   #       die "OK"; # Got whole data, not waiting for server to end the communication channel.
   #    }
   #    return 1; # In other cases make sure the handler is called for subsequent chunks
        return 1; # allow next chunk to come it...

   });

   $oHub->transport->add_handler( response_done => sub {
       my $res = shift;
       return if $opt_vt == 0;
       my $cur_time = time;
       print $debugfile "\n$cur_time === BEGIN HTTP RESPONSE DONE ===\n";
       print $debugfile $res->dump();
       print $debugfile "\n===   END HTTP RESPONSE DONE ===\n";
       return
     }
   );

      logit(0,"Survey trial of connection $connection - determine hub TEMS nodeid");
      $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM' AND NODE=THRUNODE";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      $node = $list[0]-> {NODE};
      $tems_hub_nodeid = $list[0]-> {NODE};

      if ($num_connections == 0) {
         logit(0,"Skip FTO primary node check - only one soap target");
         $got_connection = 1;
         last;
      }

      # check to see if if TGBLBRKR table is available - present on ITM 622 and later
      logit(0,"Survey trial of connection $connection - check for TGBLBRKR presence");
      $sSQL = "SELECT TABL_NAME FROM SYSTEM.SYSTABLES WHERE TABL_NAME='TGBLBRKR'";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         logit(0,"Survey failure during check for TGBLBRKR presence");
         $run_status = 0;
         next;
      }
      if ($#list == -1) {
         $DB::single=2 if $opt_debug == 1;
         logit(0,"Survey TGBLBRKR is not present so cannot check for FTO hub TEMS primary role");
         last;
      }

      logit(0,"Survey trial of connection $connection - determine hub TEMS nodeid");
      $sSQL = "SELECT NODE, THRUNODE, HOSTADDR, VERSION FROM O4SRV.INODESTS WHERE O4ONLINE='Y' AND PRODUCT='EM' AND NODE=THRUNODE";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      $node = $list[0]-> {NODE};
      $tems_hub_nodeid = $list[0]-> {NODE};
      logit(0,"Survey trial of connection $connection TEMS $node - determine if hub TEMS is in primary role");
      $sSQL = "SELECT ADDRESS, ANNOT, ENTRTYPE, PORT, PROTOCOL, ORIGINNODE FROM O4SRV.TGBLBRKR WHERE ENTRTYPE = 1 AND ORIGINNODE = \'$tems_hub_nodeid\'";
      @list = DoSoap("CT_Get",$sSQL);
      if ($run_status) {
         $DB::single=2 if $opt_debug == 1;
         $run_status = 0;
         next;
      }
      next if $#list == -1;
      logit(0,"Survey trial of connection $connection TEMS $node - has FTO primary role");
      $got_connection = 1;
      last;
   }

   if ($got_connection != 1) {
      logit(0,"Survey - no primary hub TEMS found - ending survey");
      exit 1;
   }

   my $isitname;
   my $ifullname;
   my $ipdt;
   my $iautostart;
   my $isitinfo;
   my $icmd;
   my $iautosopt;
   my $ireev_days;
   my $ireev_time;
   my $iid;
   my $iobjname;
   my $iobjclass;
   my $inodel;

   # get Situation Group IDs
   $sSQL = "SELECT ID FROM O4SRV.TGROUP WHERE GRPCLASS='2010'";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}
   foreach my $r (@list) {
       my $iid   = $r->{ID};               # Group ID
       $iid   =~ s/\s+$//;                 # trim trailing whitespace
       $gx = $grpx{$iid};
       if (!defined $gx) {
          $grpi++;
          $gx = $grpi;
          $grp[$gx] = $iid;
          $grpx{$iid} = $gx;
          $grp_sit[$gx] = {};
          $grp_grp[$gx] = {};
       }
      logit(100,"ID $iid group added");
   }

   # get Situation Group IDs and situations in the groups
   $sSQL = "SELECT ID, OBJNAME, OBJCLASS FROM O4SRV.TGROUPI WHERE GRPCLASS='2010' AND (OBJCLASS='5140' OR OBJCLASS = '2010')";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}
   foreach my $r (@list) {
       $iid    = $r->{ID};                  # Group ID
       $iid    =~ s/\s+$//;                 # trim trailing whitespace
       $iobjname = $r->{OBJNAME};     # Situation name or Group Name
       $iobjname =~ s/\s+$//;            # trim trailing whitespace
       my $iobjclass  = $r->{OBJCLASS};   # Situation or Group object id
       $gx = $grpx{$iid};
       if (!defined $gx) {
          warn "unknown group id $iid.\n";
          next;
       }
      $grp_sit[$gx]->{$iobjname} = 1 if $iobjclass == 5140;
      $grp_grp[$gx]->{$iobjname} = 1 if $iobjclass == 2010;
      logit(100,"ID $iid added to group $iobjname class $iobjclass");
   }

   # get Situation Description table data
   $sSQL = "SELECT SITNAME, PDT, AUTOSTART, SITINFO, CMD, AUTOSOPT, REEV_DAYS, REEV_TIME FROM O4SRV.TSITDESC";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 8) {
          logit(10,"working on INODESTS row $ll of $pcount has $count instead of expected 8 keys");
          next;
       }
       $isitname = $r->{SITNAME};
       $isitname =~ s/\s+$//;   #trim trailing whitespace
       if (length($isitname) > 31) {
          $advi++;$advonline[$advi] = "Situation name is greater then 31 characters";
          $advcode[$advi] = "SITAUDIT1045W";
          $advimpact[$advi] = $advcx{$advcode[$advi]};
          $advsit[$advi] = $isitname;
       }
       $iautostart = $r->{AUTOSTART};
       $iautostart =~ s/\s+$//;   #trim trailing whitespace

       $sit_tems_alert = 1 if $isitname eq "TEMS_Alert";

       # Usually ignore autostart = *NO. However if it is a SP2OS-ish UADVISOR,
       # the situation could have been auto-distributed and so report it.
       # also work on if -runall is specified.
       if ($iautostart eq "*NO") {
          if (!defined $hSP2OS{$isitname}) {
             next if $opt_runall == 0;
          }
       }
       $sit_tems_alert_run = 1 if (($isitname eq "TEMS_Alert") and ($iautostart eq "*NO"));
       $isitinfo = $r->{SITINFO};
       $isitinfo =~ s/\s+$//;   #trim trailing whitespace
       $icmd = $r->{CMD};
       $icmd =~ s/\s+$//;   #trim trailing whitespace
       $iautosopt = $r->{AUTOSOPT};
       $iautosopt =~ s/\s+$//;   #trim trailing whitespace
       $ireev_days = $r->{REEV_DAYS};
       $ireev_days =~ s/\s+$//;   #trim trailing whitespace
       $ireev_time = $r->{REEV_TIME};
       $ireev_days =~ s/\s+$//;   #trim trailing whitespace
       $ipdt = $r->{PDT};
       $ipdt =~ s/\s+$//;   #trim trailing whitespace
       newsit($isitname,$ipdt,"",$iautostart,$isitinfo,$icmd,$iautosopt,$ireev_days,$ireev_time);
   }

   # get Situation fullname table data
   $sSQL = "SELECT ID, FULLNAME FROM O4SRV.TNAME";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 2) {
          logit(10,"working on TNAME row $ll of $pcount has $count instead of expected 2 keys");
          next;
       }
       $iid = $r->{ID};
       $iid =~ s/\s+$//;   #trim trailing whitespace
       $ifullname = $r->{FULLNAME};
       $ifullname =~ s/\s+$//;   #trim trailing whitespace
       $sx = $sitx{$iid};
       next if !defined $sx;
       $sit_fullname[$sx] = $ifullname;
    }

   # get Distribution table data
   $sSQL = "SELECT OBJNAME, NODEL, OBJCLASS FROM O4SRV.TOBJACCL WHERE (OBJCLASS = '5140' OR OBJCLASS = '2010') AND SYSTEM.PARMA('QIBNODE', 'QOMEGAVIEW', 32) AND SYSTEM.PARMA('FILTER','DIRECTDIST',10)";
   @list = DoSoap("CT_Get",$sSQL);
   if ($run_status) { exit 1;}

   $ll = 0;
   $pcount = $#list+1;
   foreach my $r (@list) {
       my $count = scalar(keys %$r);
       $ll++;
       if ($count < 3) {
          logit(10,"working on TOBJACCL row $ll of $pcount has $count instead of expected 3 keys");
          next;
       }
       $iobjname = $r->{OBJNAME};
       $iobjname =~ s/\s+$//;   #trim trailing whitespace
       $iobjclass = $r->{OBJCLASS};
       $iobjclass =~ s/\s+$//;   #trim trailing whitespace
       $inodel   = $r->{NODEL};
       $inodel   =~ s/\s+$//;   #trim trailing whitespace
       if ($iobjclass eq '5140') {
          $key = " OBJA." . $inodel . " ";
          $sx = $sitx{$iobjname};
          next if !defined $sx;
          $sit_tems_alert_dist = 1 if $iobjname eq "TEMS_Alert";
          $sit_dist[$sx] = 1;
          $sit_distribution = 1;
          next if index($sit_dist_objaccl[$sx],$key) != -1;
          $sit_dist_objaccl[$sx] .= $key;
       } elsif ($iobjclass eq '2010')   {
          $gx = $grpx{$iobjname};
          next if !defined $gx;
          %sum_sits = ();
          sitgroup_get_sits($gx);
          foreach my $s (keys %sum_sits) {
             $sx =  $sitx{$s};
             next if !defined $sx;
             $sit_dist[$sx] = 1;
             $sit_distribution = 1;
             $key = " GRPA." . $inodel . " ";
             next if index($sit_dist_objaccl[$sx],$key) != -1;
             $sit_dist_objaccl[$sx] .= $key;
          }
       }
   }
}


# Get options from command line - first priority
sub init {
   my $myargs_remain;
   my @myargs_remain_array;
   use Getopt::Long qw(GetOptionsFromString);
   $myargs = shift;

   ($rc,$myargs_remain) = GetOptionsFromString($myargs,
              'log=s' => \ $opt_log,                  # log file
              'ini=s' => \ $opt_ini,                  # control file
              'user=s' => \$user,                     # userid
              'passwd=s' => \$passwd,                 # password
              'debuglevel=i' => \ $opt_debuglevel,    # log file contents control
              'debug' => \ $opt_debug,                # log file contents control
              'h' => \ $opt_h,                        # help
              'v' => \  $opt_v,                       # verbose - print immediately as well as log
              'vt' => \  $opt_vt,                     # verbose traffic - print traffic.txt
              'o=s' => \ $opt_o,                      # output file
              'a' => \ $opt_a,                        # output file
              'workpath=s' => \ $opt_workpath,        # output file
              'runall' => \$opt_runall,               # analyze Run at Startup = *Off situations
              'std' => \ $opt_std,                    # credentials from standard input
              'nodist' => \ $opt_nodist,              # credentials from standard input
              'dist' => \ $opt_dist,                  # Report on situation distribution
              'sth24' => \ $opt_sth24,                # Report STH less then 24 hours
              'agent_filter' => \ $opt_agent_filter,  # Report on agent filtering
              'syntax' => \ $opt_syntax,              # Syntax tracing
              'nohdr' => \ $opt_nohdr,                # Skip header for regression test
              'private' => \ $opt_private,            # Private Situation Audit
              'function' => \ $opt_function,          # Column Function Usage
              'txt' => \ $opt_txt,                    # txt input
              'lst' => \ $opt_lst,                    # lst input
              'bulk=s' => \ $opt_bulk_path,           # bulkexportsit directory input
              'pdtmsl' => \ $opt_pdtmsl,              # generate MSLs for duplicate PDTs
              'pdtlim=i' => \ $opt_pdtlim,            # on duplicate PDTs, lower limit on how many to report on
              'sitpdt' => \$opt_sitpdt,
              'noauto' => \ $opt_noauto,              # create editsit for impossible to run cases
              'nofull' => \ $opt_nofull,              # Do not display fullname
              'all' => \ $opt_all                     # Handle autostart *NO situations
             );
   # if other things found on the command line - complain and quit
   @myargs_remain_array = @$myargs_remain;
   if ($#myargs_remain_array != -1) {
      foreach (@myargs_remain_array) {
        print STDERR "SITAUDIT001E Unrecognized command line option - $_\n";
      }
      print STDERR "SITAUDIT001E exiting after command line errors\n";
      exit 1;
   }

   # Following are command line only defaults. All others can be set from the ini file

   if (!defined $opt_ini) {$opt_ini = "sitaudit.ini";}         # default control file if not specified
   if (!defined $opt_noauto) {$opt_noauto = 0;}                      # Don't create autostart_off commands
   if ($opt_h) {&GiveHelp;}  # GiveHelp and exit program
   if (!defined $opt_debuglevel) {$opt_debuglevel=90;}         # debug logging level - low number means fewer messages
   if (!defined $opt_debug) {$opt_debug=0;}                    # debug - turn on rare error cases
   if (!defined $opt_nofull) {$opt_nofull=0;}                  # Display Sitname and not Fullname
   if (defined $opt_txt) {
      $opt_txt_tsitdesc = "QA1CSITF.DB.TXT";
      $opt_txt_tname =    "QA1DNAME.DB.TXT";
      $opt_txt_tobjaccl = "QA1DOBJA.DB.TXT";
      $opt_txt_tgroup   = "QA1DGRPA.DB.TXT";
      $opt_txt_tgroupi  = "QA1DGRPI.DB.TXT";
      $opt_txt_evntmap  = "QA1DEVMP.DB.TXT";
      $opt_txt_tactypcy = "QA1DACTP.DB.TXT";
      $opt_txt_toverride = "QA1DOVRD.DB.TXT";
      $opt_txt_tnodelst = "QA1CNODL.DB.TXT";
      $opt_txt_tnodesav = "QA1DNSAV.DB.TXT";
      push @{$configx{"txt"}},"parm";
   }
   if (defined $opt_lst) {
      $opt_lst_tsitdesc = "QA1CSITF.DB.LST";
      $opt_lst_tsitdesc1 = "QA1CSITF1.DB.LST";
      $opt_lst_tname =    "QA1DNAME.DB.LST";
      $opt_lst_tobjaccl = "QA1DOBJA.DB.LST";
      $opt_lst_tgroup   = "QA1DGRPA.DB.LST";
      $opt_lst_tgroupi  = "QA1DGRPI.DB.LST";
      $opt_lst_evntmap  = "QA1DEVMP.DB.LST";
      $opt_lst_tactypcy = "QA1DACTP.DB.LST";
      $opt_lst_toverride = "QA1DOVRD.DB.LST";
      $opt_lst_tnodelst = "QA1CNODL.DB.LST";
      $opt_lst_tnodesav = "QA1DNSAV.DB.LST";
      push @{$configx{"lst"}},"parm";
   }
   push @{$configx{"bulk"}},"parm" if defined $opt_bulk;

   # ini control file must be present

   if (-e $opt_ini) {                                      # make sure ini file is present

      open( FILE, "< $opt_ini" ) or die "Cannot open ini file $opt_ini : $!";
      my @ips = <FILE>;
      close FILE;

      # typical ini file scraping. Could be improved by validating parameters

      my $l = 0;
      foreach my $oneline (@ips)
      {
         $l++;
         chomp($oneline);
         next if (substr($oneline,0,1) eq "#");  # skip comment line
         @words = split(" ",$oneline);
         next if $#words == -1;                  # skip blank line
          if ($#words == 0) {                         # single word parameters
            if ($words[0] eq "verbose") {$opt_v = 1;}
            elsif ($words[0] eq "traffic") {$opt_vt = 1;}
            elsif ($words[0] eq "std") {$opt_std = 1;}
            elsif ($words[0] eq "runall") {$opt_runall = 1;}            # all agents of interest
            elsif ($words[0] eq "nodist") {$opt_nodist = 1;}            # Report on Run at Startup but nodist
            elsif ($words[0] eq "dist") {$opt_dist = 1;}                # Report on Situation Distribution
            elsif ($words[0] eq "sth24") {$opt_sth24 = 1;}              # Report STH less then 24 hours
            elsif ($words[0] eq "agent_filter") {$opt_agent_filter = 1;} # Report on Agent Filtering
            elsif ($words[0] eq "private") {$opt_private = 1;}          # Perform Private Situation Audit
            elsif ($words[0] eq "function") {$opt_function = 1;}          # Perform Private Situation Audit
            elsif ($words[0] eq "syntax") {$opt_syntax = 1;}             # Syntax tracing
            else {
               print STDERR "SITAUDIT003E Control without needed parameters $words[0] - $opt_ini [$l]\n";
               $run_status++;
            }
            next;
         }

         if ($#words == 1) {
            # two word controls - option and value
            if ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "user")  {$user = $words[1];}
            elsif ($words[0] eq "passwd")  {$passwd = $words[1];}
            elsif ($words[0] eq "soapurl") {push(@connections,$words[1]);}
            elsif ($words[0] eq "soap") {$opt_soap = 1; push(@connections,$words[1]);push @{$configx{"soap"}},"ini";}
            elsif ($words[0] eq "bulk") {$opt_bulk_path = $words[1];push @{$configx{"bulk"}},"ini";}
            elsif ($words[0] eq "log") {$opt_log = $words[1];}
            elsif ($words[0] eq "o") {$opt_o = $words[1];}
            elsif ($words[0] eq "a") {$opt_a = "sit_atr.txt";}
            elsif ($words[0] eq "workpath") {$opt_workpath = $words[1];}
            elsif ($words[0] eq "soap_timeout") {$opt_soap_timeout = $words[1];}
            elsif ($words[0] eq "skip") {my $skipone= $words[1]; $hSkip{$skipone} = 1;}
            else {
               print STDERR "SITAUDIT005E ini file $l - unknown control oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         if ($#words == 3) {
            # four+ word controls - option and three values and optional message template
            if ($words[0] eq "txt") {
               $opt_txt=1;
               $opt_txt_tsitdesc=$words[1];
               $opt_txt_tname=$words[2];
               $opt_txt_tobjaccl=$words[3];
               push @{$configx{"txt"}},"ini";
            } else {
               print STDERR "SITAUDIT005E ini file $l - unknown control $oneline\n"; # kill process after current phase
               $run_status++;
            }
            next;
         }
         print STDERR "SITAUDIT005E ini file $l - unknown control $oneline\n"; # kill process after current phase
         $run_status++;
      }
   }

   # defaults for options not set otherwise

   if (!defined $opt_log) {$opt_log = "sitaudit.log";}           # default log file if not specified
   if (!defined $opt_h) {$opt_h=0;}                            # help flag
   if (!defined $opt_v) {$opt_v=0;}                            # verbose flag
   if (!defined $opt_vt) {$opt_vt=0;}                          # verbose traffic default off
   if (!defined $opt_dpr) {$opt_dpr=0;}                        # data dump flag
   if (!defined $opt_std) {$opt_std=0;}                        # default - no credentials in stdin
   if (!defined $opt_soap_timeout) {$opt_soap_timeout=180;}    # default 180 seconds
   if (!defined $opt_o) {$opt_o="sitaudit.csv";}               # default output file
   if (!defined $opt_a) {$opt_a=0;}                            # default output file
   if (!defined $opt_workpath) {$opt_workpath="";}             # default is current directory
   if (!defined $opt_runall) {$opt_runall = 0;}                # default no Run at Startup = *YES situations
   if (!defined $opt_txt) {$opt_txt = 0;}                      # default no txt input
   if (!defined $opt_lst) {$opt_lst = 0;}                      # default no lst input
   if (!defined $opt_bulk_path) {$opt_bulk = 0;}               # default no bulkexportsit input
   if (defined $opt_bulk_path) {$opt_bulk = 1;}                # default no bulkexportsit input
   if (!defined $opt_soap) {$opt_soap = 0;}                    # default no soap input
   if (!defined $opt_nodist) {$opt_nodist=0;}                  # do not advise on *YES and no distribution cases
   if (!defined $opt_dist) {$opt_dist=0;}                      # default do not report on situation distribution
   if (!defined $opt_sth24) {$opt_sth24=0;}                    # default do not report on situation distribution
   if (!defined $opt_agent_filter) {$opt_agent_filter=0;}      # default to not report on Agent Filtering
   if (!defined $opt_private) {$opt_private=0;}                # default to no Private Situation Audit
   if (!defined $opt_function) {$opt_function=0;}              # default to no Function report
   if (!defined $opt_syntax) {$opt_syntax=0;}                  # default to no syntax tracing
   if (!defined $opt_pdtmsl) {$opt_pdtmsl=0;}                  # default to no MSL creation for duplicate PDTs
   if (!defined $opt_pdtlim) {$opt_pdtlim=1;}                  # default to show cases with 5 duplicate PDTs
   if (!defined $opt_sitpdt) {$opt_sitpdt=0;}                  # default to no MSL creation for duplicate PDTs

   $opt_workpath =~ s/\\/\//g;                                 # convert to standard perl forward slashes
   if ($opt_workpath ne "") {
      $opt_workpath .= "\/" if substr($opt_workpath,length($opt_workpath)-1,1) ne "\/";
   }


   if ($opt_dpr == 1) {
#     my $module = "Data::Dumper";
#     eval {load $module};
#     if ($@) {
#        print STDERR "Cannot load Data::Dumper - ignoring -dpr option\n";
#        $opt_dpr = 0;
#     }
      $opt_dpr = 0;
   }

   # if credential as passed in via standard input, then that takes precendence.

   if ($opt_std == 1) {
      my $stdline = <STDIN>;
      if (defined $stdline) {
         my @values = split(" ",$stdline);
         while (@values) {
            if ($values[0] eq "-user")  {
               shift(@values);
               $user = shift(@values);
               die "STD option -user with no following value\n" if !defined $user;
            } elsif ($values[0] eq "-passwd")  {
               shift(@values);
               $passwd = shift(@values);
               die "STD option -passwd with no following value\n" if !defined $passwd;
            } else {
               my $rest_stdin = join(" ",@values);
               die "unknown option(s) in stdin [$rest_stdin]\n" if defined $rest_stdin;
            }
         }
      }
   }

   # complain about options which must be present
   if (($opt_bulk + $opt_txt + $opt_lst + $opt_soap) != 1) {
      print STDERR "SITAUDIT006E exactly one of bulk/txt/lst/soap must be present\n";
      if ($opt_lst != 0) {
         my $porg = join(",",@{$configx{"lst"}});
         print STDERR "SITAUDIT006E lst orinated in $porg\n";
      }
      if ($opt_txt != 0) {
         my $porg = join(",",@{$configx{"txt"}});
         print STDERR "SITAUDIT006E txt orinated in $porg\n";
      }
      if ($opt_bulk != 0) {
         my $porg = join(",",@{$configx{"bulk"}});
         print STDERR "SITAUDIT006E bulk orinated in $porg\n";
      }
      if ($opt_soap == 1) {
         my $porg = join(",",@{$configx{"soap"}});
         print STDERR "SITAUDIT006E soap orinated in $porg\n";
      }
      $run_status++;
   }
   if ($opt_soap == 1) {
      if ($#connections == -1) {
         print STDERR "SITAUDIT006E connection missing in ini file $opt_ini\n";
         $run_status++;
      }
      if ($user eq "") {
         print STDERR "SITAUDIT007E user missing in ini file $opt_ini or stdin\n";
         $run_status++;
      }
   }

   # if any errors, then dump log and exit
   # this way we can show multiple errors at startup
   if ($run_status) { exit 1;}

}


#------------------------------------------------------------------------------
# Perform soap process
#------------------------------------------------------------------------------
sub DoSoap
{
   $survey_sqls++;                             # keep count of SQLs
   $soap_faultstr = "";                             # reset fault string to null
   $soap_faultcode = "";                            # reset fault code to null
   my @results2;
   my $sql_start_time = time;
   my $mySQL;
   my $get_raw;
   my $res;
   my $result;

   my $soap_action = shift;
   if ($soap_action eq "CT_Get") {
      $mySQL = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(table => 'O4SRV.UTCTIME' ),
         SOAP::Data->name(sql => $mySQL )
      );

      logit(10,"SOAP CT_Get start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP CT_Get end [$soap_rc] - $mySQL");

   } elsif ($soap_action eq "CT_Get_Object") {
      $mySQL = shift;
      $get_raw = shift;
      $get_raw = "" if !defined $get_raw;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(object => $mySQL )
      );

      logit(10,"SOAP CT_Get_Object start - $mySQL");
      $res = $oHub->CT_Get(@aParms);
      $soap_rc = $?;
      $survey_sql_time += time - $sql_start_time;
#     sleep 10;
      logit(10,"SOAP CT_Get_Object end [$soap_rc] - $mySQL");
      return $res if $get_raw eq 'raw';                 # use raw return

   } elsif ($soap_action eq "CT_Alert") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(table => 'O4SRV.CLACTLCLO4SRV.UTCTIME' ),
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Alert start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Alert(@aParms);
      $soap_rc = $?;
      logit(10,"SOAP Alert end [$soap_rc]");

   } elsif ($soap_action eq "CT_Reset") {
      my $myAlert_name = shift;
      my $myAlert_source = shift;
      my $myAlert_item = shift;
      my $myAlert_timestamp = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(name =>      $myAlert_name),
         SOAP::Data->name(source =>    $myAlert_source),
         SOAP::Data->name(item =>      $myAlert_item),
         SOAP::Data->name(timestamp => $myAlert_timestamp),
         SOAP::Data->name(results =>   '~')
      );

      logit(10,"SOAP Reset start - $myAlert_name $myAlert_source $myAlert_item $myAlert_timestamp");
      $res = $oHub->CT_Reset(@aParms);
      $soap_rc = $?;
      #$survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP Reset end [$soap_rc]");

   } elsif ($soap_action eq "CT_WTO") {
      my $myAlert_data = shift;
      my $myAlert_severity = shift;
      my $myAlert_category = shift;

      my @aParms = (
         SOAP::Data->name(userid => $user ),
         SOAP::Data->name(password => $passwd ),
         SOAP::Data->name(table => "O4SRV.CLACTLCL" ),
         SOAP::Data->name(object => "Local_System_Command" ),
         SOAP::Data->name(data =>      $myAlert_data),
         SOAP::Data->name(category =>    $myAlert_category),
         SOAP::Data->name(severity =>      $myAlert_severity)
      );

      logit(10,"SOAP WTO start - $myAlert_data $myAlert_category $myAlert_severity");
      $res = $oHub->CT_WTO(@aParms);
      $soap_rc = $?;
      #$survey_sql_time += time - $sql_start_time;
      logit(10,"SOAP CT_WTO end [$soap_rc]");

   } else {
      logit(0,"Unknown SOAP message [$soap_action]");
      exit 1;
  }

if ($soap_rc != 0) {
   # note this possible message "read timeout at C:/Perl/site/lib/LWP/Protocol/http.pm line 433."
   # for timeout cases. Possibly want to retry at some point.
   $soap_faultstr = chop($res);
   logit(0,"ERROR $soap_rc Problem submitting SOAP Call - $soap_faultstr");
   $run_status++;
   return @results2;
}
if (substr($res,0,1) ne "<") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc SOAP Failure - $soap_faultstr");
   $run_status++;
   return @results2;
}

if (substr($res,0,6) eq "<HTML>") {
   $soap_faultstr = $res;
   logit(0,"ERROR $soap_rc non-SOAP response - $soap_faultstr");
   $run_status++;
   return @results2;
}

#  print STDERR "INFO" . "SOAP Call submitted successfully\n";
if (91 <= $opt_debuglevel) {
   logit(91,"INFO result res[$res]");
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \$res","$res");
   }
}

#

# the eval is needed to trap some illegal soap syntax and save for later analysis
eval {$result = $tpp->parse($res);};
if ($@) {
   $soap_faultstr = $@;
   logit(0,"ERROR syntax error detected by XML::Simple in the XMLin() routine");
   logit(0,"$@");
   logit(0,"INFO result res[$res]");
   $run_status++;
   return @results2;
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \$result","\$result");
   }
}

# Check for an error fault return. Call out a login failure immediately.
# pretty much any error here prevents data retrieval, stop trying

$rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'});
if ($rt eq "HASH") {
      $soap_faultstr = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultstring'};
      $soap_faultcode = $result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-ENV:Fault'}->{'faultcode'};
      logit(0,"ERROR SOAP - $soap_faultcode $soap_faultstr");
      if ($soap_faultstr eq "CMS logon validation failed.") {
         die "Logon userid/password invalid, please correct" if $soap_faultstr eq "CMS logon validation failed.";
      }
      $run_status++;
} else {
   if ($soap_action eq "CT_Get_Object") {
     if ($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{'OBJECT'} eq "Local_System_Command") {
         return @results2;
     }
   }
   $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
   if ($rt eq "ARRAY") {
      @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
   }
   elsif ($rt eq "HASH") {
       push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
   }
   else {       # check if data contained in an envelope
      $rt = ref($result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});                                       #
      if ($rt eq "ARRAY") {
         @results2=@{$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW}};
      }
      elsif ($rt eq "HASH") {
         push(@results2,$result->{'SOAP-ENV:Envelope'}->{'SOAP-ENV:Body'}->{'SOAP-CHK:Success'}->{TABLE}->{DATA}->{ROW});
      } else {
         $soap_faultstr = $res;
         logit(0,"ERROR SOAP no data  - $soap_faultstr");
         logit(0,"unknown result type [$rt] processing SOAP Call for $mySQL - missing data");
      }
   }
}

if ($opt_dpr == 1) {
   if (91 <= $opt_debuglevel) {
      datadumperlog("Data:Dumper of \@results2","\@results2");
   }
}

return @results2;
}

#------------------------------------------------------------------------------
sub GiveHelp
{
  $0 =~ s|(.*)/([^/]*)|$2|;
  print <<"EndOFHelp";

  $0 v$gVersion

  This script surveys an ITM environment looking for possibly unhealthy agents
  which are online not responsive.

  Default values:
    log           : sitaudit.log
    ini           : sitaudit.ini
    user          : <none>
    passwd        : <none>
    debuglevel    : 90 [considerable number of messages]
    debug         : 0  when 1 some breakpoints are enabled]
    h             : 0  display help information
    v             : 0  display log messages on console
    vt            : 0  record http traffic on traffic.txt file
    dpr           : 0  dump data structure if Dump::Data installed
    std           : 0  get user/password from stardard input

  Example invovation
    $0  -ini <control file> -pc ux

  Note: $0 uses an initialization file [default sitaudit.ini] for many controls.

EndOFHelp
exit;
}


#------------------------------------------------------------------------------
# capture log record
sub logit
{
   my $level = shift;
   if ($level <= $opt_debuglevel) {
      my $iline = shift;
      my $itime = gettime();
      chop($itime);
      my $oline = $itime . " " . $level . " " . $iline;
      if ($opt_debuglevel >= 100) {
         my $ofile = (caller(0))[1];
         my $olino = (caller(0))[2];
         if (defined $ofile) {
            $oline = $ofile . ":" . $olino . " " . $oline;
         }
      }
      print FH "$oline\n";
      print "$oline\n" if $opt_v == 1;
   }
}

#------------------------------------------------------------------------------
# capture agent log record
#------------------------------------------------------------------------------
# capture agent error record

# write output log
sub datadumperlog
{
   require Data::Dumper;
   my $dd_msg = shift;
   my $dd_var = shift;
   print FH "$dd_msg\n";
   no strict;
   print FH Data::Dumper->Dumper($dd_var);
}

# return timestamp
sub gettime
{
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;
   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   return sprintf "%4d-%02d-%02d %02d:%02d:%02d\n",$year+1900,$mon+1,$mday,$hour,$min,$sec;
}

# get current time in ITM standard timestamp form
sub get_timestamp {
   my $sec;
   my $min;
   my $hour;
   my $mday;
   my $mon;
   my $year;
   my $wday;
   my $yday;
   my $isdst;

   ($sec,$min,$hour,$mday,$mon,$year,$wday,$yday,$isdst)=localtime(time);
   $year += 1900;
   $mon += 1;


   my $nyy = substr("00" . $year,-2,2);
   my $nmo = substr("00" . $mon,-2,2);
   my $ndd = substr("00" . $mday,-2,2);
   my $nhh = substr("00" . $hour,-2,2);
   my $nmm = substr("00" . $min,-2,2);
   my $nss = substr("00" . $sec,-2,2);

   my $etime = "1" . $nyy . $nmo . $ndd . $nhh . $nmm . $nss . "000";  # check time in ITM 16 byte format
   return $etime;
}

# Following logic replicates most of the tacmd processing logic to determine the
# protocol and port number required to access ITM Web Services or SOAP. For input
# it uses the soapurl supplied by the user. From this the following is discovered
#   1) Is a forced protocol supplied  - https or http
#   2) Is a port number supplied
# The natural SOAP URL will be accessed using a remote command with no content. That will verify the userid and password.
# If an error results, then the index.xml file is retrieved and parsed to determine if there is a better port to use
# There are various error conditions that can result and will cause a failure. The most common case
# is be a TEMS behind a firewall that only allows port 3661 access. If the hub TEMS is recycled, the SOAP access
# port would be an ephemeral one. The port number could be discovered in the index.xml data but access would fail.
# In any case, an error message will show what needs to be done.

# SOAP::Lite does not support http6 or https6 at the current level and so that processing is present but
# blocked at present.

sub get_connection {
my $opt_soap_lite_v6 = 0;            # Change to 1 when SOAP::Lite supports http6 and https6
                                     # This allows the support for http6/https6 to be present but not effect processing
my $connect_protocolGiven = 0;       # when 1, soapurl contains a known protocol
my $connect_portGiven = 0;           # when 1, soapurl contains a port number
my $connect_attempthttps = 0;        # when 1, attempt access by https
my $connect_attempthttps6 = 0;       # when 1, attempt access by https6 [ future SOAP::Lite ]
my $connect_attempthttp = 0;         # when 1, attempt access by http
my $connect_attempthttp6 = 0;        # when 1, attempt access by http6  [ future SOAP::Lite ]
my $connect_httpPortNo = "";         # http port number found in index.xml results
my $connect_httpsPortNo = "";        # https port number found in index.xml results
my $connect_ip6PortNo = "";          # http6 port number found in index.xml results   [ future SOAP::Lite ]
my $connect_ips6PortNo = "";         # https6 port number found in index.xml results  [ future SOAP::Lite ]
my $connect_rest;                    # section of soapurl with protocol removed
my $connect_hostName;                # section of soapurl identified as hostname [or ip address] of the server running hub TEMS
my $connect_port;                    # port used to access SOAP server
my $connect_protocol;                # protocol used to access SOAP
my $connect_res;                     # results returned from SOAP
my $test_connection;                 # trial connection string
my $connect_httpsFound;              # during index.xml analysis, https port found
my $connect_httpFound;               # during index.xml analysis, http port found
my $connect_https6Found;             # during index.xml analysis, https6 port found [ future SOAP::Lite ]
my $connect_http6Found;              # during index.xml analysis, http6 port found  [ future SOAP::Lite ]
my $result;
my @results3;                        # array used in parsing top level index.xml results
my @results4;                        # array used in parsing second level index.xml results
my $in_protocol;                     # protocol from index.xml results

   logit(0,"Determine proper SOAP connection based on [$connection]");

   # stage 1, analyze the given connection string

   if (substr($connection,0,8) eq "https://") {                           # user supplied https
      $connect_protocol = "https";
      $connect_attempthttps = 1;
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } elsif (substr($connection,0,9) eq "https6://") {                     # user supplied https6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "https6";
      $connect_attempthttps6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,9);

   } elsif (substr($connection,0,7) eq "http://") {                       # user supplied http
      $connect_protocol = "http";
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,7);

   } elsif (substr($connection,0,8) eq "http6://") {                      # user supplied http6, future SOAP::Lite logic
      $DB::single=2 if $opt_debug == 1;
      next unless $opt_soap_lite_v6 == 1;
      $connect_protocol = "http6";
      $connect_attempthttp6 = 1;
      $connect_protocolGiven = 1;
      $connect_rest = substr($connection,8);

   } else {
      $connect_attempthttps = 1;                                          # user did not supply protocol, try https and then http
      $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_attempthttp = 1;
      $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      $connect_rest = $connection;
   }

   # Stage 2, get the port number if one supplied
   if (index($connect_rest,':') != -1) {
      $connect_rest =~ m/(\S+):(\d+)/;
      $connect_hostName = $1;
      $connect_port = $2;
      $connect_portGiven = 1;
   } else {
      $connect_hostName = $connect_rest;
      $connect_port = "";
   }

   # stage 3, if port number was given but not protocol
   #           if port is associated with protocol then select that protocol
   #           otherwise try https and then http

   if (($connect_port ne "") and  ($connect_protocolGiven == 0)) {
      if ($connect_port == 3661) {
         $connect_attempthttp = 0;
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;

      } elsif ($connect_port == 1920) {
         $connect_attempthttp = 1;
         $connect_attempthttps = 0;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;

      } else {
         $connect_attempthttps = 1;
         $connect_attempthttps6 = 1 if $opt_soap_lite_v6 == 1;
         $connect_attempthttp = 1;
         $connect_attempthttp6 = 1 if $opt_soap_lite_v6 == 1;
      }
   }

   # Stage 4 create trial connection string based on attempt settings

   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;
      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }
      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
      logit(0,"Trial SOAP connection based on [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);          # set Soap::Lite controls
      $oHub->outputxml('true');                                                               # require xml output
      $oHub->on_fault( sub {});      # pass back all errors                                   # pass back error conditions
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command');                          # attempt connection
      $run_status = 0;                                                                        # reset failure counter, since only resting
      if ($soap_rc == 0) {                                                                         # if good return code and empty fault string, then declare success
         if ($soap_faultstr eq "") {
            logit(0,"SOAP connection success [$test_connection]");
            $connection = $test_connection;
            return 0;
         }
      }

      # Prior to ITM 6.2, there was different logic. At the moment this is not supported.
      # For the record the logic looked in the results and did the following
      #   search for "Service Point"
      #   look ahead for <  and find sevice name within <>
      #   ignore if not "cms"
      #   look ahead for ":"
      #   look ahead for second ":"
      #   select characters until "/"
      #   result is alternate port number
      # try that as alternate port to access SOAP
   }

   # if not successful yet, work by retrieving the index.xml file
   #  This contains full information about what services are registered and the port number

   logit(0,"Trial SOAP connection failed, work with index.xml file");
   for (my $i=0; $i < 4; $i++) {
      if (($i == 0) and ($connect_attempthttps == 1)) {
         $connect_protocol = 'https' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'https6' if $connect_protocolGiven == 0;
         $connect_port = '3661' if $connect_portGiven == 0;

      } elsif (($i == 2) and ($connect_attempthttp == 1)) {
         $connect_protocol = 'http' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;

      } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
         $DB::single=2 if $opt_debug == 1;
         $connect_protocol = 'http6' if $connect_protocolGiven == 0;
         $connect_port = '1920' if $connect_portGiven == 0;
      } else {
         next;
      }

      $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "/kdh/index/index.xml";
      logit(0,"Attempt retrievel of index.xml file using [$test_connection]");
      $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
      $oHub->outputxml('true');
      $oHub->on_fault( sub {});      # pass back all errors
      $connect_res = DoSoap('CT_Get_Object','Local_System_Command','raw');       # the 'raw' third parm means that DoSoap will not analyze results
      $run_status = 0;                                                           # reset error count
      next if $soap_rc != 0;                                                          # if severe error
      next if $soap_faultstr ne "";                                                   # or soap_faultstring, then exit
      next if substr($connect_res,0,1) ne '<';                                   # something bad happenned like timeout, ignore it

      eval {$result = $tpp->parse($connect_res)};                                # attempt to parse results
      if ($@ ne "") {
         logit(100,"error parsing index.xml results $@");
         next;
      }

      next if ref($result->{'kdh:servicepointlist'}->{'servicepoint'}) ne "ARRAY";  # array expected, else quit

      push(@results3,@{$result->{'kdh:servicepointlist'}->{'servicepoint'}});

      $connect_httpPortNo = "";                                                 # reset all potential results
      $connect_httpsPortNo = "";
      $connect_ip6PortNo = "";
      $connect_ips6PortNo = "";
      $connect_httpsFound = 0;
      $connect_httpFound = 0;
      $connect_https6Found = 0;
      $connect_http6Found = 0;

      foreach my $rr (@results3) {                                               # top level scan of services, looking for one that ends up "_cms"
         next if substr($rr->{'#text'},-4,4) ne '_cms';
         push(@results4,@{$rr->{'location'}->{'protocol'}});                     # capture protocol array
         foreach my $ss (@results4) {
            $in_protocol = $ss->{'#text'};
            if ($in_protocol eq "ip.ssl") {
               $DB::single=2 if $opt_debug == 1;
               $connect_httpsPortNo = $ss->{'endpoint'};
               $connect_httpsFound = 1;
            } elsif ($in_protocol eq "ip.tcp") {
               $connect_httpPortNo = $ss->{'endpoint'};
               $connect_httpFound = 1;
            } elsif ($in_protocol eq "ip6.ssl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ips6PortNo = $ss->{'endpoint'};
               $connect_https6Found = 1;
            } elsif ($in_protocol eq "ip6.tcpl") {
               $DB::single=2 if $opt_debug == 1;
               next unless $opt_soap_lite_v6 == 1;
               $connect_ip6PortNo = $ss->{'endpoint'};
               $connect_http6Found = 1;
            }
         }
      }

      # update the attempt variables based on the ports found
      $connect_attempthttps = 0;
      $connect_attempthttp  = 0;
      $connect_attempthttps6  = 0;
      $connect_attempthttp6  = 0;
      $connect_attempthttps = 1 if $connect_httpsPortNo ne "";
      $connect_attempthttp  = 1 if $connect_httpPortNo ne "";
      $connect_attempthttps6  = 1 if $connect_ips6PortNo ne "";
      $connect_attempthttp6  = 1 if $connect_ip6PortNo ne "";

      for (my $i=0; $i < 4; $i++) {
         if (($i == 0) and ($connect_attempthttps == 1)) {
            $DB::single=2 if $opt_debug == 1;
            $connect_protocol = 'https';
            $connect_port = $connect_httpsPortNo;
         } elsif (($i == 1) and ($connect_attempthttps6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'https6';
            $connect_port = $connect_ips6PortNo;
         } elsif (($i == 2) and ($connect_attempthttp == 1)) {
            $connect_protocol = 'http';
            $connect_port = $connect_httpPortNo;
         } elsif (($i == 3) and ($connect_attempthttp6 == 1)) {
            $DB::single=2 if $opt_debug == 1;
            next unless $opt_soap_lite_v6 == 1;
            $connect_protocol = 'http6';
            $connect_port = $connect_ip6PortNo;
         } else {next;}

         $test_connection = $connect_protocol . "://" . $connect_hostName . ":" . $connect_port . "///cms/soap";
         logit(0,"Trial SOAP connection based index.xml [$test_connection]");
         $oHub = SOAP::Lite->proxy($test_connection,timeout => $opt_soap_timeout);
         $oHub->outputxml('true');
         $oHub->on_fault( sub {});      # pass back all errors
         $connect_res = DoSoap('CT_Get_Object','Local_System_Command');
         $run_status = 0;
         if ($soap_rc == 0) {
            if ($soap_faultstr eq "") {
               logit(0,"SOAP connection success [$test_connection]");
               $connection = $test_connection;
               return 0;
            }
         }
      }  # end of analysis if single index.xml file
   }  # end of attempt to retrieve index files
logit(0,"unable to establish connection to SOAP server");
$run_status++;
}

# History log

# 1.00000  : New script based on ITM Health Survey 1.08000
# 1.01000  : Handle attribute names with extended characters
# 1.02000  : Handle *MISSING values better
#          : Add Advisories including syntax and first two MS_OFFLINE related
# 1.03000  : Add more advisor messages
# 1.04000  : Add in distribution logic  including -nodist option to show
#          : add -nohdr for regression testing, add 1019/1020 messages
#          : incorporate FULLNAME when avail
# 1.05000  : Advise *MIN/*MAX
#          : Advise on *TIME with same attribute group table test
#          : add opt_dist and opt_agent_filter
#          : Situation Group distribution logic and make Agent filter report optional
# 1.06000  : Advise on action command run every interval
# 1.07000  : Handle command *NONE better and a short AUTOSOPT case
# 1.08000  : Add -syntax, handle *HISTRULE condition
# 1.09000  : Advisory on process/filesystem and *COUNT/etc
#          : Distinguish action command every interval on Agent and on TEMS
# 1.10000  : Handle action commands running on TEMS better.
# 1.11000  : Handle bulkexportsit better, add advisory on some multi-row cases if atomized
# 1.12000  : Advisory for action commands using attribute groups not in situation formula
#          : Sort report file for repeatability
# 1.13000  : remove action command from 1028E advisory, problems with regression testing
#          : Add four new advisories on historical data collection
#          : Add an advisory on TEMS_Alert available and not running
# 1.14000  : Do not warn on built-in substitutions
#          : Add Process Filter and numeric column function advisory.
#          : Add *VALUE xxx *GE 0 advisory
#          : Add *SCAN *NE with wildcard advisory
#          : Add skip control to cancel specific message codes
# 1.15000  : Correct report titles
#          : Advisory on situation name subset issue
#          : Advisories on reev_days and reev_time
#          : Advisory on subset situations
# 1.16000  : handle literals with just periods and digits, test for zero better
# 1.17000  : Handle *COUNT and process counts
#          : Advisory on NT_Event_Log and Description/Description_U
# 1.18000  : Advisory on sampled Unicode attributes with wildcard tests
# 1.19000  : add -private to report on potential private situations
# 1.20000  : improve -private report based on system admin manual
#          : add -function to report on situation function usage
# 1.21000  : refine V8 private reporting
# 1.22000  : Handle PDT not starting *IF
# 1.23000  : Handle "blank" situation definition by ignoring it
# 1.24000  : Handle 32 character TSITDESC.SITNAME cases
# 1.25000  : add -a option, warn on mixed time attributes
# 1.26000  : Better logic for mixed pure and sampled groups in formula
#          : Add -lst logic
# 1.27000  : add advisory for A UNTIL B and B all pure
# 1.28000  : add advisory for A UNTIL B, A and B have different DisplayItems
#          : Add advisory for looping *SITs and capture included Attribute Groups
#          : Add top 20 changed situations
# 1.29000  : better parse_lst logic, handle null chunks
# 1.30000  : Detect multi-row DisplayItem conflict
# 1.31000  : Detect wrong length value test in LocalTime and UniversalTime
#          : detect two or more multi-row attribute groups
# 1.32000  : handle KfwSQLClient anomaly, extra space when not expected
# 1.33000  : Add domain test for Local_Time.Hours
# 1.34000  : Add check for fileinfo path without file
#          : Add advisory for too many correlated situations
# 1.35000  : Add check for multi-row base and different multi-row Until
# 1.36000  : Add advisory for *TIME tests with *EQ/*NE and for tests against future time
# 1.37000  : Add report on multiple PFT usages
# 1.38000  : Add advisory on 32 character situation names
#          : Add -pdtmsl to report on and generate recovery files on too many situations case
# 1.39000  : Add -noauto to set RunOnStartup=No on impossible situations
# 1.40000  : Add -nofull to use sitname in reports and to produce report on sitname and fullname
#          : Correct some defects related to -bulk option
# 1.41000  : Correct -lst options
#          : Embedded report and advisory explanations
#          : improved logic on sampled to pure to sampled coercion
# 1.42000  : Correct *SCAN *NE test and explanation 1036W
#          : Correct MS_ONLINE and MS_OFFLINE type counts
# 1.43000  : Add formula counts to summary
# 1.44000  : anominize two example report rows
# 1.45000  : Add advisory for pure situations with *COUNT test

# Following is the embedded "DATA" file used to explain
# advisories and reports.
__END__

SITAUDIT0999E
Text: Syntax error - [<sitname>] [<predicate>]

Meaning: The situation is probably not behaving as expected.

The Situation formula or predicate is composed in a mini-language.
Occasionally a parse error is encountered. In most cases the TEMS data
file has a formula that is simply bad. For example one recent case was

*IF *MISSING NT_Process.Process_Name *EQ ( 'lsass','services,'svchost' )

Notice the missing single quote after 'services.  Another case showed a
single colon character. That is just incorrect syntax.

It is often impossible to discover how this occurred. It might have been
a product defect or a mistaken tacmd editSit command, where syntax is
not checked. If the situation is expected to run, it should be corrected
by deleting and rewriting the situation.

Recovery Plan: The situation should be re-authored to accomplish
what is required or deleted if not needed.
--------------------------------------------------------------

SITAUDIT1000E
Text: MS_Offline type - <sitname> - missing Reason *NE FA testSITAUDIT0999E

Meaning: The situation will usually create floods of events at ITM
transition periods such as at hub TEMS startup

MS_Offline type situations are used to identify managed systems [Agents]
which are not delivering periodic node status updates. This can arise
for many reasons: system failure, communications problems, agent logic
problems, system environmental problems and agent configuration problems
and many more. It is an important tool for awareness agent status.

During transition periods the Reason attribute is set to the value FA
[Framework Architecture]. During those periods the *OFFLINE status does
not reflect reality. For example, just as a hub TEMS is starting up all
the agents appear to be offline. There is a default grace period set of
12 minutes to allow the agents to connect and send node status. During
that period, a MS_Offline type situation must not create situation
events. That is accomplished by adding this test to the situation formula

    *AND Reason *NE FA

You can observe this in the unmodified product provided MS_Offline
situation

At ITM 623 FP5 and ITM 630 FP2 logic was added to cover additional
transition cases - a remote TEMS recycle or a FTO [Hot Standby]
switch from one hub to another.

Recovery Plan: Rewrite any indentified MS_Offline type situation formula
include the Reason test.
--------------------------------------------------------------

SITAUDIT1001E
Text: MS_Online type - <sitname>

Meaning: This type of situation results in a very severe hub TEMS load
and can destabilize ITM processing. This has been seen rarely, perhaps
twice in 10 years.

MS_Online is typically a clone of the MS_Offline situation but checking
for *ONLINE instead of *OFFLINE. The usual goal is to gain awareness
of new agents connecting.

The goal is worthy but the ITM implementation of the needed record
keeping causes severe hub TEMS stress. In the several observed cases,
the hub TEMS was unstable and stopped after several days.

I will be explaining the technical background of this issue and the
related MS_Offline with Persist>1 case. It is too complex for this
type of document.

Recovery Plan: Stop the MS_Online type situation and delete it.
--------------------------------------------------------------

SITAUDIT1002E
Text: MS_Offline type - <sitname> - always just 1 row

Meaning: The situation will not behave as expected.

MS_Offline type situation events are created by hub TEMS logic. The
events are formulated as though they arrived from the agent. That is
nonsense of course because the agent itself is not reporting. This fact
has an important effect on column functions.

The various column functions do arithmetic or each agent separately.

*COUNT/*AVG/*SUM/*MIN/*MAX/*CHANGE/*PCTCHANGE

In this case the *COUNT is always exactly one, the *AVG is always the
current value, etc. Logically the functions have no real usage or
meaning in this context. The damage is done when the user expects to
get an alert of something important and it gets created. That is a pure
waste of time and effort. The costs escalate if the customer involves
IBM Support to "resolve" this condition.


Recovery Plan: Delete the situation and design another way to achieve
the desired goal
--------------------------------------------------------------

SITAUDIT1003E
Text: Too many MS_Offline type situations [<count>] vs nominal [<nominal>]

Meaning: The hub TEMS may experience instability including failure.

MS_Offline type situations are resource intensive to run. At each
sampling interval, a large table needs to be read entirely. This table
is 516 bytes per row so 10,000 agents will require reading about
5 megabytes of data. If you have 10 MS_Offline type situations which are
evaluated once every 2 minutes, the steady state rate is about 400K
bytes per second. During each situation evaluation process a lock is
held, which delays many other activities. That can lead to relatively
low CPU use along with an inability to keep up with normal work.

One case involved about 3000 agents and 13 MS_Offline type situations
evaluating at 1 minute. The system running the TEMS was not very
powerful. The result was hub TEMS instability. At times the hub was so
busy it could not respond to remote TEMS activity for minutes at a time.
That convinced the remote TEMS the hub TEMS was offline. After a few
days, the hub TEMS failed for out of storage. The most extreme case was
a customer with 83 MS_Offline type situations and the hub TEMS was
almost non-operational.

This should be avoided at all costs. If you need significant numbers of
MS_Offline type alerts, that logic should be created in the event
receiver and *not* via multiple situations.

The nominal value has been set to alert if there are more then 5
MS_Offline type situations.


Recovery Plan: Carefully consider how many MS_Offline type situations to
run. Plan to do significant logic at the event receiver instead of using
this type of situation.
--------------------------------------------------------------

SITAUDIT1004E
Text: MS_Offline type - <sitname> - with Persist>1

Meaning: The hub TEMS may experience instability including failure.

MS_Offline type situations with persist>1 are extremely resource
intensive to run. Without persist>1 the situation evaluation logic is
contained mostly in the TEMS Data Server [SQL processor]. Once an agent
is identified as being in the offline status, no added work send to
SITMON process as long as the agent remains in the offline status. When
it eventually becomes online again, a status is sent.

With Persist>1 SITMON must process every single offline agent on every
sampling interval. That includes a complete scan of the Situation Status
Cache table, which can have thousands of entries. That scan is for every
single offline agent every time.

If there are relatively few offline agents and the Situation Status
Cache is small, this may not cause much overhead. Otherwise the SITMON
workload becomes gigantic and can easily result in hub TEMS instability
or actual failure.

If you absolutely must use this construction, make the sampling interval
large. The effect is multiplied if there are multiple such situations.

Recovery Plan: Avoid using MS_Offline with Persist > 1.
--------------------------------------------------------------

SITAUDIT1005E
Text: MS_Offline type - <sitname> - action command

Meaning: The hub TEMS may experience instability including failure.

Action commands are processed using the same address space as the ITM
Process. If there are a large number of events suddenly , the ITM
process can experience instability including failure.

Most situations cannot generate a large number of events at the same
time. However MS_Offline can create many events at once. For example, if
an Agentless Agent Server has 800 monitored systems and  the Agentless
Agent Server is stopped to apply maintenance, all 800 monitored agents
will be declared offline at the same time.

Until ITM 623 FP5 and ITM 630 FP3, if a remote TEMS is recycled or
communication is lost every single agent connected through that remote
TEMS will be declared offline at the same time.

When that happens hundreds or thousands of action commands will be
generated at once. This often results in a dramatic increase in process
storage and an increase in the number of threads. The common result is
that the hub TEMS becomes unstable and usually fails. It is fine for the
typical case of one or two agents going offline randomly, but the mass
offline needs to be avoided.

Recovery Plan: Avoid using MS_Offline with action commands.
--------------------------------------------------------------

SITAUDIT1006E
Text: MS_Offline type - <sitname> - Action command must be configured to TEMS

Meaning: The defined action command will never run.

If you absolutely *must* have a MS_Offline type situation with an action
command, the action command must be configured to execute at the TEMS.
This sort of situation is a probe type and in those cases an action
command configured to execute at the agent will be silently ignored.

Recovery Plan: For a MS_Offline type situation, configure action command
to run a TEMS.
--------------------------------------------------------------

SITAUDIT1007E
Text: MS_Offline type - <sitname> - Sampling interval [<num> seconds] smaller then nominal [<num> seconds]

Meaning: The TEMS maybe be unstable.

MS_Offline situations are very resource intensive. In addition, there is
as much as a 13 minute delay between the offline condition and recording
of that status at the hub TEMS. A sampling interval should be selected
to balance the two objectives of expense and timeliness.

Currently the nominal value is 5 minutes.

If you  require very fast response to a system or service outage,
MS_Offline never the best choice. Instead consider some sort of ping to
the service.

Recovery Plan: Avoid running MS_Offline type situations at low sampling
intervals.
--------------------------------------------------------------

SITAUDIT1008E
Text: Too many MS_Offline evaluations per hour -[<num>] nominal [<num>]

Meaning: The TEMS maybe be unstable.

MS_Offline type situations are very resource intensive.  A large file
has to be processed for every situation evaluation. This process
calculates the estimated number of evaluations per hour from all
MS_Offline type situations and generates an advisory if there are more
then 75 Per hour. That would be true if there were 7 situations being
evaluated every 5 minutes.

This alert is generated if there are more then 75 evaluations per hour.

Recovery Plan: Increase the sampling interval or decrease the number of
MS_Offline type situations.
--------------------------------------------------------------

SITAUDIT1009E
Text: Multiple tables in situation [<sitname>] tables [<table list>]

Meaning: Possible TEMS performance problems

ITM Agents can only run situation against a single attribute group. The
TEP Situation Editor allows creation of situations with multiple
attribute groups. This is accomplished by creating hidden sub-situations
which are run in a coordinated way to accomplish the goal.

Such multiple attribute group situations should be evaluated for
efficiency. In one case a seeming simple situations resulted in
22 sub-situations and an enormous workload both on the TEMS and the Agent.

The Local_Time and Universal_Time attribute groups are not counted for
this advisory. They typically have a minimal impact.

Recovery Plan: Avoid composing situations using multiple attribute groups.
--------------------------------------------------------------

SITAUDIT1010W
Text: Situation [<sitname>] has *SIT tests

Meaning: Possible TEMS performance problems

A ITM situation formula can test against other situations by using
the *SIT comparison test.

This is valid and useful, but it can result in excessive load on the
TEMS the agent connects to. The most efficient situations do most of the
work on the Agent and only send work to the TEMS when there is a
possible error condition. When *SIT tests are present, the results
have to be sent to the TEMS on every cycle. In one such case 25% of the
 TEMS workload was composed of a single situation like this.

Such situations with *SIT tests should be evaluated for efficiency.

Recovery Plan: Increase the sampling interval or rewrite the situation
for increased efficiency.
--------------------------------------------------------------

SITAUDIT1011E
Text: Situation [<sitname>] has multiple *COUNT tests [<count>]

Meaning: Situation will not work as expected

It is possible to author a situation with OR conditions each one having
a separate *COUNT tests. However the actual *COUNT test value will
always be the size of the total result rows, not the rows associated
with each sub-clause of the formula.

Recovery Plan: Divide the situation into multiple situations and only
use a single *COUNT tests.
--------------------------------------------------------------

SITAUDIT1012E
Text: Situation [<sitname>] has *COUNT test against 0

Meaning: Situation will not work as expected

A *COUNT test value will be 1 at the least. If there were no rows, no
result rows would be transmitted and the TEMS evaluation would never
take place.

Recovery Plan: The only way to test for no rows is the *MISSING column
function.
--------------------------------------------------------------

SITAUDIT1013W
Text: Situation [<sitname>] has *COUNT test with *LE/*LT 1

Meaning: Situation will not work as expected

A *COUNT test value will be 1 at the least. If there were no rows, no
result rows would be transmitted and the TEMS evaluation would never
take place.  The *LT 1 can never happen. The *LE 1 strongly suggest the
author expects it to fire when 0 - which can never happen.

Recovery Plan: The only way to test for no rows is the *MISSING column
function.
--------------------------------------------------------------

SITAUDIT1014E
Text: Situation [<sitname>] has *COUNT test with *LE/*LT

Meaning: Situation will not work as expected

A *COUNT test value will be 1 at the least. If there were no rows, no
result rows would be transmitted and the TEMS evaluation would never
take place.  The *LT or *LE suggests the author might think the
count included the case 0 - which can never happen.

Recovery Plan: The only way to test for no rows is the *MISSING column
function. That almost always needs a second situation.
--------------------------------------------------------------

SITAUDIT1015W
Text: Pure Situation [<sitname>] has *UNTIL/*SIT [<sitname>]

Meaning: Situation will not work as expected

Pure situations with *UNTIL/*SIT are unreliable when the TEMS is under
very heavy load. Two results send in one order from the Agent may be
processed in the reverse order. An *UNTIL/*SIT depends on the second
suppressing the first. The actual processing of the second before the
first can cause unexpected alerts.

*UNTIL/*SIT logic was designed for sampled situations. In fact online
help for the Situation Editor explicitly suggest not using it for pure
situations. It will certainly work when events are arriving at a slow
place, but not reliably.

Recovery Plan: Avoid using UNITL/*SIT for Pure situations.
--------------------------------------------------------------

SITAUDIT1016W
Text: Pure Situation [<sitname>] has Persist>1

Meaning: Situation will not work as expected

Pure situations are generated one at a time and always in a true state.
There is never a N or close status. Because of the Persist has no real
meaning. At best it could be confusing.

Recovery Plan: Avoid using Persist>1 for Pure situations.
--------------------------------------------------------------

SITAUDIT1017W
Text: Sampled Situation [<sitname>] has *UNTIL/*TTL [<time>]

Meaning: Situation will not always work as expected

The *UNTIL/*TTL is designed for pure situations - to automatically close
events. This should not be used for sampled situations for several
reasons.

First, the agent is unaware of the change in status. If you have an
action command which runs at the agent at every interval, it will keep
on running even though the situation appears closed.

Second, there will be a period of time when the condition appears
cleared even though the issue still exists. This is a relatively short
period since at the next evaluation interval the agent will send new
results and a new situation event will be created. However it is like a
burglar alarm which has been reset without determining the intruder has
left. It is just not a good idea.

Recovery Plan: Avoid using *UNITL/*TTL for Sampled Situations.
--------------------------------------------------------------

SITAUDIT1018W
Text: Sampled Situation [<sitname>] with *UNTIL/*SIT needs Persist=3

Meaning: Situation will not always work as expected

The *UNTIL/*SIT processing can show timing problems where the UNTIL
situation results are not processed in time to suppress the base
situations. To avoid this set the Persist to 3.

Recovery Plan: For *UNTIL/*SIT on sampled situations set Persist=3.
--------------------------------------------------------------

SITAUDIT1019I
Text: Situation [<sitname>] is Run at Startup but no distribution

Meaning: This informational message is produced only when the -nodist
option is set.

It might be a situation that was intended to run. It might be a
situation that was temporarily turned off. Whatever the cause, the
situation should be carefully considered as to what exactly is required.

Recovery Plan: Review need for this situation.
--------------------------------------------------------------

SITAUDIT1020W
Text: Sampled Situation [<sitname>] less then 30 second sampling time [<seconds>]

Meaning: Potential severe performance impact.

The Situation Editor enforces a lower limit sampling rate of 30 seconds.
There are various ways to circumvent that limitation but it can cause a
severe performance impact.

As long as a condition remains true, the agent will send the result rows
every sampling interval. Therefore the need should be reviewed and
justified.

Recovery Plan: Review need for sub 30 second sampling interval.
--------------------------------------------------------------

SITAUDIT1021W
Text: *MIN/*MAX [<sitname>] are unreliable

Meaning: Situation will not work as expected.

The *MIN and *MAX column functions work somewhat randomly. Because of
this they should not ever be used.

The impact appears to be very small. A survey of large customers showed
no usage at all.

Recovery Plan: Delete situation and find another way to alert
on condition.
--------------------------------------------------------------

SITAUDIT1022W
Text: *TIME [<sitname>] same attribute group tested

Meaning: Situation will not work as expected.

The *TIME comparison test only works correctly when time stamps are
compared from different tables. Any test between two attributes in the
same table will not works.

In practical use, the test is usually against LocalTime.Time or
UniversalTime.Time . That time is the time at the TEMS the agent
connects to. That also means that time zone differences need to be taken
into account unless the agent and the TEMS are in the same time zone.

Recovery Plan: Change test to match the above requirement
--------------------------------------------------------------

SITAUDIT1023W
Text: Sampled Situation [<sitname>] with Action Command running every interval

Meaning: Situation may have severe performance impact.

One of the Situation Action command options is to run at every interval
on the agent. This can be extremely resource intensive when the sampling
interval is short.

Recovery Plan: Set the "run at every interval" off unless you can
justify the cost.
--------------------------------------------------------------

SITAUDIT1024E
Text: Sampled Situation [<sitname>] with Action Command on TEMS running every interval

Meaning: Situation often has severe performance impact on TEMS.

One of the Situation Action command options is to run at every interval
on the TEMS. This can be extremely resource intensive when the sampling
interval is short and when there are many agents. This condition alone
has been seen to make a TEMS unstable.

Recovery Plan: Set the "run at every interval" off unless you can
justify the cost.
--------------------------------------------------------------

SITAUDIT1025W
Text: Arithmetic test on Process situation [<sitname>] [<pdt>]

Meaning: Situation often has severe performance impact on TEMS.

The arithmetic column functions *COUNT/*AVG/*SUM cause all result rows
to be sent to the TEMS for evaluation. There are often several hundred
processes. When many agents do the same thing the TEMS can go unstable.

Recovery Plan: If you must make such a test, chose a sampling interval
as long as possible. For example if the condition is rare, make a
sampling interval of one day.
--------------------------------------------------------------

SITAUDIT1026W
Text: Arithmetic test on File Information situation [<sitname>] [<pdt>]

Meaning: Situation often has severe performance impact on TEMS.

The arithmetic column functions *COUNT/*AVG/*SUM cause all result rows
to be sent to the TEMS for evaluation. There are often hundreds of files.
When many agents do the same thing the TEMS can go unstable.

Recovery Plan: If you must make such a test, chose a sampling interval
as long as possible. For example if the condition is rare, make a
sampling interval of one day.
--------------------------------------------------------------

SITAUDIT1027W
Text: Arithmetic test on Multi-row Attribute Group situation [<sitname>] [<pdt>]

Meaning: Situation often has severe performance impact on TEMS.

The arithmetic column functions *COUNT/*AVG/*SUM cause all result rows
to be sent to the TEMS for evaluation. In a multi-row attribute group
there may be many such rows and this can severely impact a TEMS.

Recovery Plan: If you must make such a test, chose a sampling interval
as long as possible. For example if the condition is rare, make a
sampling interval of one day.
--------------------------------------------------------------

SITAUDIT1028E
Text: Action command attribute group(s) [<bad_tables>] not in Situation Formula [<cmd>]

Meaning: Situation does not behave as expected

Situations can have action commands with substitutions. The
substitutions must reflect the attribute groups available and used in
the Situation Formula. When this is not true the action command will not
have all expected data. This typically happens when the
Situation Formula was changed after configuring the action command.

Recovery Plan: Recreate the situation command using the now available
substitutions.
--------------------------------------------------------------

SITAUDIT1029W
Text: UADVISOR situation may populate hub TEMS virtual table

Meaning: Situation may cause hub TEMS instability

Some older agents use a UADVISOR situation to automatically maintain a
hub TEMS virtual table. These virtual tables are not used these days.
Depending on the number of agents involved, this can result in hub TEMS
instability. That shows in remote TEMS and agents going on and off line.

The agents involved are
UX - Unix OS Agent
OQ - Agent for Microsoft SQL
OR - Agent for Oracle
OY - Agent for Sybase
Q5 - Agent for Microsoft Clustering
HV - Agent for Microsoft Hyper-V Server


One APAR fix was created concerning this issue and so on recent ITM
levels there will be no issue with Unix OS Agent.

IV47363 - SITUATION UADVISOR_OMUNX_SP2OS MUST BE DISABLED BY DEFAULT.

Recovery Plan: See the following as a guide to resolving the issue

https://ibm.biz/BdRW3z
--------------------------------------------------------------

SITAUDIT1030W
Text: UADVISOR History collection of Process data

Meaning: Situation may cause excess TDW collection

The Linux/Unix/Windows process attribute group can be selected for
historical data collection. In many cases this represents a significant
portion of the data collection.

The result is excess use of disk storage for the Short Term History
files. There is also a significant amount of communications required.
The STH 24 hour trimming process has to process a lot of data. The TDW
itself may require significant amount of disk storage.

The data itself is often little used and it can not be summarized.

Recovery Plan: Review the collection policy and eliminate collecting
Process if possible. If Process data is absolutely required for some
systems, make sure it is only collected on those systems and not
generally. Increase the sampling interval to reduce to impact.
--------------------------------------------------------------

SITAUDIT1031I
Text: Historical Data Collection at TEMS

Meaning: Situation may cause excess TEMS workload

Best practice is to collect historical data on the TEMA or Agent. That
reduces the workload on the TEMS and also allows the agent to collect
historical data when the TEMS is not operational.

One reason to collect on the TEMS is to reduce the Agent disk storage
requirements. However that should be weighed against the increased
centralization which creates more widespread failures. Potential
failure cases of excess disk storage usage can be controlled using
the TEMA KHD_TOTAL_HIST_MAXSIZE environment variable.

Recovery Plan: Review the collection policy and collect on the Agent
unless there are good reasons not too.
--------------------------------------------------------------

SITAUDIT1032I
Text: Historical Data Collection Export less then 24 hours
[only displayed when -sth24 option set]

Meaning: Situation may cause excess Historical Export workload

Best practice is to export historical data every 24 hours. The Portal
Client will always get the most recent 24 hours from the agent, even if
the data is already in the TDW. Each export process requires the local
Short Term History file to be read and copied to a temporary file while
skipping the data older then 24 hours. If you collect at 15 minutes,
that means the STH file is copied 96 times. Other work on the agent is
likely more important. Also at 24 hours the process will be done at
midnight when workload is often lower.

If the TDW data is being used by another process like analytics studies,
keeping it up to date may be work the cost. But even then typical
studies review the last weeks or months and not the last few hours. That
is how to avoid costly crises.

Recovery Plan: Review the export policy and consider switching to a
24 hour collection cycle.
--------------------------------------------------------------

SITAUDIT1033W
Text: TEMS_Alert defined but not running

Meaning: No alerts for Filter too Big objects

Some situations have a formula that is too large to transmit to the
Agent. This often generates a performance disaster at the remote TEMS
where the agent connects to.

The product provided situation TEMS_Alert will create Enterprise level
alerts when such situations are started. The situations still run but
the developer and operations are warned of the potential issue so it
can be corrected immediately. The Situation Event Workspace has
references to  Web pages that fully explain the background, the impact
and how to correct the situation.

Recovery Plan: Edit the situation, set to Run on Startup, set
Distribution to *ALL_CMS and then start the situation. When events show,
investigate and correct the problem situations. This will proactively
defend against a potentially devastating performance problem.
--------------------------------------------------------------

SITAUDIT1034W
Text: Process Filter with numeric column function does not work

Meaning: Situation does not produce correct results

Process Filter attributes are available in Linux OS Agent
and Unix OS Agent.

If a numeric column function like *COUNT is added, the results are sent
to the TEMS for evaluation by the TEMS Dataserver [SQL] component. The
dataserver does not perform Process Filter logic and so the work cannot
be completed.

Recovery Plan: Do not use Process Filter attribute groups with numeric
column functions.
--------------------------------------------------------------

SITAUDIT1035W
Text: *VALUE test with always true *GE 0 test pdt[<PDT>]

Meaning: Situation may be inefficient

A situation formula test with *GE 0 or *GE 0.0 will always be true for
numeric attributes. Therefore that condition is not required for the
formula. This may represent an error in construction or simply an
oversight.

However it has common use in setting up a periodic action command and
so is rated a low impact.

Recovery Plan: Review necessity for such a test.
--------------------------------------------------------------

SITAUDIT1036W
Text: *SCAN with *NE check works like a *VALUE *NE test pdt[<PDT>]

Meaning: Situation may not work as expected

The *SCAN function in a situation only works with the *EQ test.

The *NE test is exactly equivalent to *VALUE attribute *NE test.

Recovery Plan: Rework situation to perform required logic. You can
often rework this into a Base/Until formulation where the *SCAN
with the valid *EQ test is in the Until situation.
--------------------------------------------------------------

SITAUDIT1037I
Text: Situation a superset of other sits [$psits]

Meaning: Situation may cause a TEMS crash

On very rare occasions that subset name condition can cause TEMS crashes.
The TEMS workload must be very high.  This issue documented by
APAR IV55058 and corrected in ITM 623 FP5 and ITM 630 FP3.

Recovery Plan: If this is a concern, upgrade the TEMS maintenance level
or rename the subset situations to avoid this issue.
--------------------------------------------------------------

SITAUDIT1038W
Text: Situation Reevaluate days must be 1 to 3 characters long

Meaning: Situation may not operate as expected

The REEV_DAYS must be from 1 to 3 digits long, representing
0 to 999 days. If this is different then reevaluation may not proceed
as expected.

Recovery Plan: Update the Situation and set a conforming day.
--------------------------------------------------------------

SITAUDIT1039W
Text: Situation Reevaluate time must be 6 characters long

Meaning: Situation may not operate as expected

The REEV_TIME must be 6 digits long, representing hhmmss. If this is
different then reevaluation may not proceed as expected.

Recovery Plan: Update the Situation and set a conforming day.
--------------------------------------------------------------

SITAUDIT1040E
Text: Situation has *COUNT test with Linux/Unix Process_Count attribute

Meaning: Situation may have excessive overhead.

The example is *COUNT KLZ_Process.Process_Count *LT 4. The *COUNT causes
a row for every process to be sent to the TEMS. This can cause extreme
overhead and possible TEMS instability. This also applies to
Linux_Process.Process_Count [earlier Linux] and
Process.Process_Count [Unix].

In many cases this should be *VALUE KLZ_Process.Process_Count *LT 4.
This works if each row has an identical command line, which is often
true. This results in no TEMS overhead at all unless the problem
condition exists. You also need a second situation with a *MISSING
clause since there is no other way to test for that case.

Recovery Plan: Rewrite the situation if at all possible. If that is not
possible because the command lines are different, then increase the
sampling interval to reduce the overall TEMS impact
--------------------------------------------------------------

SITAUDIT1041W
Text: Action Command substitution NT_Event_Log Description/Description_U

Meaning: Action command may not operate as expected

The NT_Event_Log attributes Description and Description_U are 1128 bytes
long. A Situation action command has a length of 1024 characters or less.
If the description happens to be quite long, then the command maybe
silently truncated, giving incorrect results.

Another issue is that the Description text may contain meta characters
important to the command line processing. One common example is "don't"
where the single quote will usually cause a command line syntax error
and the action command not running.

Recovery Plan: Review the situation action command and thoroughly test
before using. It may be necessary to remove that attribute substitution
to get a consistent action command.
--------------------------------------------------------------

SITAUDIT1042W
Text: *IN and *CHANGE together in a situation formula can cause TEMS crash until before ITM 623 FP2

Meaning: Situation may crash the TEMS the agent connects to

A situation with both *IN and *CHANGE can crash the TEMS.
See APAR IV24119. This issue was corrected at maintenance level
ITM 623 FP2.

Recovery Plan: Update the TEMS maintenance level… or stop the situation
from running.
--------------------------------------------------------------

SITAUDIT1043W
Text: Count of *IN values $sit_inct[$i] greater then nominal 15

Meaning: Situation may create severe performance problems on the TEMS.

A situation with too many *IN tests may often create a WHERE clause that
is too large to transmit to the Agent. In this circumstance, the agent
may run in unfiltered mode and send tremendous number results to the
TEMS for filtering. The exact number of *IN tests is not predictable and
depends on the size of the strings being tested and other factors.

See this post for more details.

Sitworld: Situation Limits
https://ibm.biz/BdRZSy

Recovery Plan: Divide the situation into situations with 15 or fewer *IN
tests. Avoid having more then one *IN test.
--------------------------------------------------------------

SITAUDIT1044W
Text: Unicode attribute with wildcard [*] value tests

Meaning: Situation may create performance problems on the Agent

When a Unicode attribute is used in a situation formula and the test
uses a wildcard character, the agent CPU resource will often be much
higher then expected. The reason is that Unicode comparison is quite
expensive involving calls to external routines. When a wild card is
present there can be many such tests.

Recovery Plan: If possible change the situation to not use Unicode
attributes or to avoid the use of wildcard tests. For example on
Process type situations, use a Process Filter for initial filtering and
then a non-wildcard test comparison.
--------------------------------------------------------------

SITAUDIT1045W
Text: Situation name is greater than 31 characters

Meaning: Situation may fail if melded into duperized situation

From ITM 620 situation names had to be 31 characters or less. For longer
names or when unusual characters were used, a FULLNAME is created and
the Situation name is an index. Some early situations remain which are
32 characters long. If they are subject to a melding into a duperized
situation, the combined situation fails. See the following for more
information:

Sitworld: Super Duper Situations
https://ibm.biz/BdXX7Y

Recovery Plan: If needed, the situation should be rewritten from scratch
with a name 31 characters long or less.
--------------------------------------------------------------

SITAUDIT1046E
Text: Pure Situation has UNTIL/*SIT [until_sit] which is pure sit without any *UNTIL

Meaning: Situation will often not work as expected.

This is a case with two pure situations

SITA *UNTIL/*SIT SITB
SITB

If SITB fires first it will remain open forever - or until it is
manually closed. In that case SITA will always be suppressed and will
never fire.
Recovery Plan: Pure situations and *UNTIL/*SIT is unreliable and the
Portal Client Situation Editor help file specifically warns against it.
If the pure events arrive relative slowly, the following combination
will often work.

SITA *UNTIL/*SIT SITB
SITB *UNTIL/*SIT SITA

That works because each becoming open will close the other which has the
desired activity. However if the results arrive quickly than then can be
processed out of order which would prevent expected functioning. The
potential situation events are also processed in alphabetical order by
situation name, which can also prevent expected functioning. With slow
arrival, perhaps a minute or more apart and a relatively unloaded TEMS
the above will often work.
--------------------------------------------------------------

SITAUDIT1047E
Text: Attribute Group coerced from Pure to Sampled in sit[sitname] pdt[pdt]

Meaning: Situation may not work as expected and has been seen to cause
rare TEMS failures.

When a situation formula contains multiple attribute groups it may
produce a severe performance issue - see discussion on SITAUDIT1009E.
If the mixture is a pure attribute group mixed with a time test, the
situation will be invalidly converted to a sampled situation and the
results will not be as expected. In addition that condition can cause a
rare TEMS failure.

Recovery Plan: Change the formula to not mix pure and sampled attribute
groups. Often the sampled group formula can be converted to
a *UNTIL/*SIT with the same logic. This does not cause problems. Here is
an example of using a Until Situation with a time formula which can be
used to suppress a pure situation event.

Sitworld: Suppressing Situation Events By Time Schedule
https://ibm.biz/BdXBs4
--------------------------------------------------------------

SITAUDIT1048E
Text: Base Situation uses displayItem[atom] and *UNTIL/*SIT [sitname] uses different displayItem[atom]

Meaning: Situation may not work as expected.

Base situation with Until situation where both situations use a
DisplayItem only work as expected when both displayItems are the same
attribute group and attribute value. When this is not true, a Unit
situation result being true will close all Base situation events
regardless of displayItem.

Recovery Plan: Change the situation to handle correct logic.
--------------------------------------------------------------

SITAUDIT1049E
Text: Situation with looping *SIT evaluations [$loopsit]

Meaning: Situation may not work as expected.

A situation can reference other situation true status. Theoretically
that could result in a logical loop where sit_a references sit_b
references sit_a. At this best the situation might not work, at worst
it might cause a TEMS failure.

Recovery Plan: Change the situation to avoid looping situation
references.
--------------------------------------------------------------

SITAUDIT1050E
Text: Situation with multi-row attribute group [$group1] but without a DisplayItem

Meaning: Situation may not create all expected results

When a situation uses a multi-row attribute group, multiple situation
events can be created. If no DisplayItem is specified, only a single
situation event will be created. Because of that expected situation
events may be hidden. In one recent case, multiple situation events were
opened and never closed mysteriously. When a DisplayItem was added,
there were more situation events created and they were valid.

This is set to Impact 50 since this might be a deliberate choice… just
giving a single example of the issue instead of all issues. A second
reason is that an original develop engineer told me it was a design
choice. On the other hand, experiencing issues including hidden
situation events just doesn't feel right.

Recovery Plan: Add a DisplayItem to the situation definition to allow
multiple results to be returned.
--------------------------------------------------------------

SITAUDIT1051E
Text: Local_Time or Universal_Time test with incorrect attribute length check(count) [formula]

Meaning: Situation may not work as expected

The Local_Time and Universal_Time attributes are strings and not
numbers. That means that if you want to test Hour 9 of the day, the
correct test value is 09. When that is incorrect, the formula will not
test as expected. This is performed against Hours, Minutes, Seconds,
Time and DayOfWeek.

Recovery Plan: Make sure Hours, Minutes, Seconds and DayOfWeek has a
two character test value. Make sure Time has a six character test value.
--------------------------------------------------------------

SITAUDIT1052E
Text: Situation with count multi-row attribute groups [groups]

Meaning: Situation may not work as expected

Situation formulae must have only a single multi-row attribute group.
The Situation Editor enforces that rule. However a formula can be
composed and installed with [for example] tacmd editSit. If that is
done the situation does not work as expected and such situations have
been known to cause severe remote TEMS performance problems.

Recovery Plan: Delete such situations and reconsider how to make that
test. One example is here:

Sitworld: Policing the Hatfields and the McCoys
http://ibm.biz/Bd4bpr
--------------------------------------------------------------

SITAUDIT1053E
Text: Situation Formula always evaluates false - [pdt]

Meaning: Situation is likely not working as expected

A domain check analysis showed that the formula could never be true.
At this first delivery the check applies to a formula on having
Local_Time.Hours. The inspiring case was this

*IF Local_Time.Hours *LE 05 *AND Local_Time.Hours *GE 17

After quite some effort, we noticed this formula could never be true.
The *AND should have been an *OR. Anyway, to speed up future such
efforts [at least in some cases] this advisory was added.

Recovery Plan: Rethink the situation.
--------------------------------------------------------------

SITAUDIT1054E
Text: Situation formula with Path and no File in formula

Meaning: Situation often creates severe TEMS performance problem

Results are sent to the TEMS for every single file in the directory.

Recovery Plan: Rethink the situation.
--------------------------------------------------------------

SITAUDIT1055W
Text: NT_Event_Log Situation formula without Log_Name

Meaning: Situation often creates severe Agent performance problem.

More Event logs data is retrieved than necessary.

Recovery Plan: Add a Logname test.
--------------------------------------------------------------

SITAUDIT1056W
Text: Correlated Situations [num] ISITSTSH scans [num] per hour - more than 12

Meaning: Situation often creates severe hub TEMS performance problem.

The ISITSTSH scans are quite expensive. Clients with 110 and 62
correlated situations experienced hub TEMS crashes.

Recovery Plan: Use just a few correlated situations and do not evaluate
very often.
--------------------------------------------------------------

SITAUDIT1057W
Text: Situations with different multi-row attributes on BASE[$btable] and UNTIL[$utable]

Meaning: Situations will not monitor as expected.

When both base and until situation are multi-row, the TEMS will not be
able to align the results and thus the results will not be as expected.

Recovery Plan: Rethink the situation solution
--------------------------------------------------------------

SITAUDIT1058E
Text: TIME delta test with *EQ or *NE which is never correct

Meaning: Situation will never fire

Time tests between to environments [Agent and TEMS] will never be equal
and will likely always be different. Thus there is no monitoring
usefulness.

Recovery Plan: Rethink the situation solution
--------------------------------------------------------------

SITAUDIT1059W
Text: *TIME delta test which implies test for future time [pdt]]

Meaning: Situation will not behave as expected

Time tests which suggest a future time at the agent are rarely of value.
Thus the situation is probably not monitoring as needed.

Recovery Plan: Rethink the situation. Work out example times on paper
first before writing situation
--------------------------------------------------------------

SITAUDIT1060W
Text: SITNAME is 32 bytes long - illegal and will be usually ignored - fullname [$ifullname]

Meaning: From ITM 6.2 Situation names have been limited to 31 bytes
or less. If there is a longer name defined, the TNAME table is used.

Some user and product defined situation names can still be 32 bytes
long. The only impact is that some TACMD functions will refused to
operate.

If that is important, reauthor the situation with a shorter name
and delete this situation.

SITREPORT001
Text: Summary Report

Sample:
Total Situations,3299
Total Active Situations,2140
Advisory messages,301
Filter at TEMS,116
Filter at Agent,2024

Explanation: information only.
----------------------------------------------------------------

SITAUDIT1061E
Text: Attribute Group [name] coerced from Pure to Sampled in sit[sitname] pdt[pdt]

Meaning: Situation may not work as expected and has been seen to cause
rare TEMS failures.

When a situation formula contains multiple attribute groups it may
produce a severe performance issue - see discussion on SITAUDIT1009E.
If the mixture is a pure attribute group mixed with a time test, the
situation will be invalidly converted to a sampled situation and the
results will not be as expected. In addition that condition can cause a
rare TEMS failure.

Recovery Plan: Change the formula to not mix pure and sampled attribute
groups. Often the sampled group formula can be converted to
a *UNTIL/*SIT with the same logic. This does not cause problems. Here is
an example of using a Until Situation with a time formula which can be
used to suppress a pure situation event.

Sitworld: Suppressing Situation Events By Time Schedule
https://ibm.biz/BdXBs4

SITREPORT001
Text: Summary Report

Sample:
Total Situations,3299
Total Active Situations,2140
Advisory messages,301
Filter at TEMS,116
Filter at Agent,2024

Explanation: information only.
----------------------------------------------------------------

SITAUDIT1062W
Text: Pure Situation [name] has *COUNT test which test which can cause TEMS instability [pdt]

Meaning: Situation will likely not work since *COUNT only has meaning
in a Sampled Situation. The Impact level is high [95] because it will
cause TEMS instability. The *COUNT causes all results to be
sent to the TEMS with no filtering at all - higher result workload.

Recovery Plan: Change the formula to remove the *COUNT clause.
----------------------------------------------------------------

SITAUDIT1063E
         $advi++;$advonline[$advi] = "Pure Situation [$sit_psit[$i]] has Persist>1 which can never occur [$sit_pdt[$i]]";
Text: Pure Situation [name] has Persist>1 which can never occur [pdt]

Meaning: Persist is a Sampled situation concept and will never occur
on a Pure situation. As a result this situation will never fire and
so potential situation events will never be seen.

Recovery Plan: Change the formula to chagne Persist to the default 1.
----------------------------------------------------------------

SITREPORT002
Text: Top 20 most recently added or changed Situations

Sample:
LSTDATE,Situation,Formula
1190108105433000,kph_webfault_xd4m_soa_rtdi1,*IF (*VALUE Services_Inventory_610.Interval_Status *GE 2 *AND *VALUE Services_Inventory_610.Fault_Count *GE 10) *AND ((*VALUE Services_Inventory_610.Port_Namespace_U *EQ 'www.ibm.com/DPNon-XML' *AND *VALUE Services_Inventory_610.Service_Name_U *EQ 'Multiprotocol Gateway:MPG_RetrieveDrugImage_v1')),
1190108105432000,kph_maxresp_xd4m_soa_rtdi1,*IF (*VALUE Services_Inventory_610.Interval_Status *GE 2 *AND *VALUE Services_Inventory_610.Max_Elapsed_Time *GE 120000) *AND ((*VALUE Services_Inventory_610.Port_Namespace_U *EQ 'www.ibm.com/DPNon-XML' *AND *VALUE Services_Inventory_610.Service_Name_U *EQ 'Multiprotocol Gateway:MPG_RetrieveDrugImage_v1')),

Explanation:
When a problem is seen, sometimes it is caused by a recently created
situation. This report shows you the most recent 20 situations added
or changed.
----------------------------------------------------------------

SITREPORT003
Text: Situations with TEMS Filtering Report

Sample:
Fullname,Filter,PDT
KXA_License_Exp_Crit,tems,"*IF *TIME KXA_LICENSE_DETAILS.ExpirationDate *LE 'Local_Time.Timestamp + 15D' *AND *TIME KXA_LICENSE_DETAILS.ExpirationDate *GT 'Local_Time.Timestamp + 0D'"
KXA_License_Exp_Warn,tems,"*IF *TIME KXA_LICENSE_DETAILS.ExpirationDate *LE 'Local_Time.Timestamp + 30D' *AND *TIME KXA_LICENSE_DETAILS.ExpirationDate *GT 'Local_Time.Timestamp + 15D'"
KXA_License_Expired,tems,"*IF *TIME KXA_LICENSE_DETAILS.ExpirationDate *LE 'Local_Time.Timestamp + 0D'"

Explanation:
Situations need to have agent data filtered. That means an examination
of the attribute values and how they correspond with the supplied
formula. This shows situations that must be filtered at the TEMS the
agent is connected to.

When Filtering happens at the TEMS. the TEMS is impacted more. If you
are seeing TEMS overhead higher than expected, this is one thing to
check.
----------------------------------------------------------------

SITREPORT004
Text: Situations with Agent Filtering Report

Parm: Add -agent_filter

Sample:
Fullname,Filter,PDT
Apache_Site_failed,agent,"*IF *VALUE Apache_Web_Sites.Server_Failures_Rate *GT 1.000"
BesClientPagingTest1,agent,"*IF *VALUE K07_CUSTOMSCRIPT.MonitoringSolution *EQ 'bes1' *AND *VALUE K07_CUSTOMSCRIPT.Numeric *GE 15"
BesClientPagingTest2,agent,"*IF *VALUE K07_CUSTOMSCRIPT.MonitoringSolution *EQ 'bes1' *AND *VALUE K07_CUSTOMSCRIPT.RCDESC *EQ 'SUCCESS'"

Explanation:
Situations need to have agent data filtered. That means an examination
of the attribute values and how they correspond with the supplied
formula. This shows situations that are filtered at the Agent.
----------------------------------------------------------------

SITREPORT005
Text: Situation with Distributions Report

Parm: Add -dist

Sample:
Situation,Autostart,Distribution
Apache_Site_failed,*YES, OBJA.*CAM_APACHE_WEB_SERVER
BesClientPagingTest1,*YES, OBJA.Wzatsu71:07
BesClientPagingTest2,*YES, OBJA.Wzatsu71:07

Explanation:
Information about how sitautions are distributed.
----------------------------------------------------------------

SITREPORT006
Text: Situation Formula appearing in more than count situations

Sample:
,Count,Situations
*IF (*VALUE Services_Inventory_610.Interval_Status *GE 2 *AND *VALUE Services_Inventory_610.Fault_Count *GE 10) *AND ((*VALUE Services_Inventory_610.Port_Namespace_U *EQ 'http://svc.kp.org/PtCareSupport/PHISharing/KPHCsendInbasketMessage/v1' *AND *VALUE Services_Inventory_610.Service_Name_U *EQ 'KPHCsendInbasketMessageV1Port')),
,9,b017832432 b049601062 b846123878 c30923726 c893050797 d134434700 e170111837 e201832006 e68926151
*IF (*VALUE Services_Inventory_610.Interval_Status *GE 2 *AND *VALUE Services_Inventory_610.Fault_Count *GE 10) *AND ((*VALUE Services_Inventory_610.Port_Namespace_U *EQ 'urn:Epic-com:Clinical.2011.Services.Patient' *AND *VALUE Services_Inventory_610.Service_Name_U *EQ 'EpicClinicalGSPatientServices2011Port')),
,9,c033482793 c241896155 c356755130 c37176503 c709914087 d42240482 d558190238 d884805562 h21933793

Explanation:
When identical formula are used in multiple situations, the TEMS
workload increases. In the worst case this can destablize the TEMS.

It also can cause confusion since if the need arises to change a
formula, it can be that much harder to determine which situations
should be changed.

Avoid replicating a situation formula. Instead make a single situation
and distribute it to the required agents.
----------------------------------------------------------------

SITREPORT007
Text: Sitname Fullname Summary

Parm: -nofull

Sample:
sitname,fullname,
Apache_Site_fai1445532505166200,Apache_Site_failed
K_96_ServiceDown_Mirth,K_96_Postgres_Down_Mirth
K_GB_Availability_Data_Collecti,K_GB_Availability_Data_Collection

Explanation:
Show the Situation Name and Fullname correspondence. There is a
difference when the situation name does not follow short name
requirements:

1) 31 characters or less
2) Alphanumeric and underline _
3) First Character Alpha
4) Last Character not underline

It can also be used when a situation is renamed.

This is information and might be useful in interpreting agent
operations logs.
----------------------------------------------------------------
SITREPORT008
Text: Correlated Situations Report

Parm: none

Sample:
Situation,
MON_HUB_NTa_SVCS_MSSQLSERVERS_UGUNHPAAL_UGUNHPAAM_ SQLA_CLUST_C,
MON_HUB_NTa_SVCS_MSSQLSERVERS_UGUNHPAAL_UGUNHPAAM_ SQLB_CLUST_C,

Explanation:
Correlated situations are very expensive if there are many
agents. In one case a site with 5000 agents and 13 correlated
situations caused a TEMS crash once a day.

Minimize the use of correlated situations.
----------------------------------------------------------------
