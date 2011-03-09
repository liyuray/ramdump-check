use strict;
use warnings;
use Carp;
use Data::Dumper;
use utf8;
use Getopt::Long;
use Benchmark;
use Sys::Hostname;
use Math::BigInt;
use File::stat;
use Time::localtime;

our $VERSION = do { my @r = ( q$Revision: 14019 $ =~ /\d+/g ); sprintf "%d." . "%02d" x $#r, @r };

$SIG{__DIE__}  = sub { Carp::confess(@_) };
$SIG{__WARN__} = sub { Carp::cluck(@_) };

sub file_get_chunk {
    my $fh   = shift;
    my $off  = shift;
    my $size = shift;
 
    seek $fh, $off, 0;
    Carp::confess "died!" if $size < 0;
    read( $fh, my $buf, $size );

    return $buf;
}

#BEGIN { $SIG{__WARN__} = sub { $DB::single=1; } }
package Elf;

=comment

typedef struct {
  Elf32_Word	sh_name;
  Elf32_Word	sh_type;
  Elf32_Word	sh_flags;
  Elf32_Addr	sh_addr;
  Elf32_Off	sh_offset;
  Elf32_Word	sh_size;
  Elf32_Word	sh_link;
  Elf32_Word	sh_info;
  Elf32_Word	sh_addralign;
  Elf32_Word	sh_entsize;
} Elf32_Shdr;

SHT_NULL	0
SHT_PROGBITS	1
SHT_SYMTAB	2
SHT_STRTAB	3
SHT_RELA	4
SHT_HASH	5
SHT_DYNAMIC	6
SHT_NOTE	7
SHT_NOBITS	8
SHT_REL	9
SHT_SHLIB	10
SHT_DYNSYM	11
SHT_LOOS	0x60000000
SHT_HIOS	0x6fffffff
SHT_LOPROC	0x70000000
SHT_HIPROC	0x7fffffff
SHT_LOUSER	0x80000000
SHT_HIUSER	0xffffffff

=cut

sub _gen_vir2off {
    my $fhe   = shift;
    my $psech = shift;

    my @const_secs =
	sort { $psech->{$a}{1}[1] <=> $psech->{$b}{1}[1] }
	    grep { (exists $psech->{$_}{1}) && ($psech->{$_}{1}[1] > 0) }
		keys %{$psech};

    return sub {
        my $vir = shift;
        for (@const_secs) {
            my $sec_entry = $psech->{$_}{1};    # 1 means PROGBITS
            my ( $addr, $off, $size ) = @{$sec_entry}[ 1 .. 3 ];

            #	    next if $addr < 0x08000000;
            next if ( $vir - $addr ) >= $size;
            return ( $vir - $addr ) + $off;
        }
        return;
      }
}

sub _get_section_headers {
    my $fhe = shift;
    ## read elf header
    seek $fhe, 0, 0;
    read $fhe, my ($buf), 52;
    my $shoff     = unpack "L", substr( $buf, 32, 4 );
    my $shentsize = unpack "S", substr( $buf, 46, 2 );
    my $shnum     = unpack "S", substr( $buf, 48, 2 );
    my $shstrndx  = unpack "S", substr( $buf, 50, 2 );

    #	print $shoff, " ", $shentsize, " ",$shnum;

    ## read section headers
    seek $fhe, $shoff, 0;
    read $fhe, $buf, $shentsize * $shnum;

    #	print bytes::length($buf),$/;

    ## read section header string table
    my $shstroff  = unpack "L", substr( $buf, $shstrndx * $shentsize + 16, 4 );
    my $shstrsize = unpack "L", substr( $buf, $shstrndx * $shentsize + 20, 4 );
    my $shstrtab;
    seek $fhe, $shstroff, 0;
    read $fhe, $shstrtab, $shstrsize;

    #	print $shstrtab,$/;
    #	print bytes::length($shstrtab),$/;

    my %sech;
    my $p = 0;

    while ( $p < $shentsize * $shnum ) {
        my $name_off = unpack "L",  substr( $buf,      $p, 4 );
        my $name     = unpack "Z*", substr( $shstrtab, $name_off );
        my $type     = unpack "L",  substr( $buf,      $p + 4, 4 );
        my $addr     = unpack "L",  substr( $buf,      $p + 12, 4 );
        my $off      = unpack "L",  substr( $buf,      $p + 16, 4 );
        my $size     = unpack "L",  substr( $buf,      $p + 20, 4 );
        my $entsize  = unpack "L",  substr( $buf,      $p + 36, 4 );
        $sech{$name}{$type} = [ $p, $addr, $off, $size, $entsize ];
        $p += $shentsize;
    }
    return \%sech;
}

sub new {
    my $class = shift;
    my $fn    = shift;
    open my $fh, "<", $fn or die $! . ": cannot find $fn!", $/;
    binmode $fh;
    my $psech = _get_section_headers($fh);
    my $vir2off = _gen_vir2off( $fh, $psech );
    return bless {
        fn      => $fn,
        fh      => $fh,
        psech   => $psech,
        vir2off => $vir2off,
    }, $class;
}

sub get_section_off {
    my $this = shift;
    my $ph   = shift;

    return @{ $this->{psech}{ $ph->{name} }{ $ph->{type} } };
}

sub vir2off {
    my $this = shift;
    my $addr = shift;
    return $this->{vir2off}($addr);
}

sub get_octet {
    my $this = shift;
    my $off  = shift;
    my $len  = shift;

    seek $this->{fh}, $off, 0;
    read $this->{fh}, ( my $ret ), $len;
    return $ret;
}

package Sym;

sub _get_symbols {
    my $elfh = shift;

    my ( $strshentoff, undef, $strtaboff, $strtabsize, undef ) =
      $elfh->get_section_off( { name => '.strtab', type => 3 } )
      ;    # type 3 is strtab

#    my $strtaboff     = unpack "L", substr($buf, $strshentoff+16, 4); # FIXME: hardcoded .strtab
#    my $strtabsize    = unpack "L", substr($buf, $strshentoff+20, 4); # FIXME: hardcoded .strtab

    my $strtab;

    #    seek $fhe, $strtaboff, 0;
    #    read $fhe, $strtab, $strtabsize;
    $strtab = $elfh->get_octet( $strtaboff, $strtabsize );

    #	print $strtab,$/;
    #	print bytes::length($strtab),$/;

    ## read symbol table

    my ( $symentoff, undef, $symoff, $symsize, $symentsize ) =
      $elfh->get_section_off( { name => '.symtab', type => 2 } )
      ;    # type 2 is symtab

    #    my $symoff        = unpack "L", substr($buf, $symentoff+16,4);
    #    my $symsize       = unpack "L", substr($buf, $symentoff+20,4);
    #    my $symentsize    = unpack "L", substr($buf, $symentoff+36,4);

    my $symtab;

    #    seek $fhe, $symoff, 0;
    #    read $fhe, $symtab, $symsize;
    $symtab = $elfh->get_octet( $symoff, $symsize );

    #	print $symentsize,$/;
    #	print $symsize,$/;
    #	print bytes::length($symtab),$/;

    my %hash;
    my @syms;
    my $p = 0;
    while ( $p < $symsize ) {
        my ( $name, $value, $size, $info ) = unpack "LLLC",
          substr( $symtab, $p, $symentsize );
        $p += $symentsize;
        Carp::confess "died!$size" if $size < 0;

#	next if $name < 20 and $size == 0; # ignore first several names like $a,$b,$d,$t.
        next
          if ( ( $info & 0xf ) != 1 && ( $info & 0xf ) != 2 )
          ;    # only care about OBJECT==1, FUNC==2
               #		printf("0x%08x %8d ", $value, $size);
               #		print(unpack("Z*", substr($strtab, $name)));
        my $str =
          substr( $strtab, $name, index( $strtab, "\0", $name ) - $name );
        next
          if $str =~
              /^[\|\$\.]/;    # ignore section names like .bssxxx. $a, $b, $d, $t.

        #	print join(",", $name, $value, $size, $info, $str), $/;
        my %shash;
        $shash{Value} = $value;
        $shash{Size}  = $size;
        $shash{Type}  = ( ( $info & 0xf ) == 1 ) ? "OBJECT" : "FUNC";

        #The same variable name problem.
        my $i = 0;
        while ( exists $hash{$str} )
        {
            $str = $str."_SameNameItem$i";
        }

        $hash{$str}   = \%shash;

        #		print $str, " ", sprintf("0x%08x",$shash{Value}),$/;
        push @syms, $str;
    }
    $hash{undermap}{Value} = 0;
    $hash{undermap}{Size}  = 0;
    $hash{undermap}{Type}  = 'undef';
    unshift @syms, 'undermap';
    @syms = sort { $hash{$a}{Value} <=> $hash{$b}{Value} } @syms;
    $hash{yjlist} = \@syms;
    return \%hash;
}

sub _binary_search {
    my $phash = shift;
    my $nl    = shift;
    my $nr    = shift;
    my $addr  = shift;

    return $nl if ( $nr - $nl ) <= 1;
    my $n = int( ( $nl + $nr ) / 2 );

#	printf "##dbg: %10d %10d 0x%08x 0x%08x %s$/", $nl, $nr, $phash->{$phash->{yjlist}[$n]}{Value}, $addr, $phash->{yjlist}[$n];
    return _binary_search( $phash, $n, $nr, $addr )
      if $addr >= $phash->{ $phash->{yjlist}[$n] }{Value};
    return _binary_search( $phash, $nl, $n, $addr );
}

sub new {
    my $class = shift;
    my $elfh  = shift;
    my $phash = _get_symbols($elfh);
    return bless {
        elfh  => $elfh,
        phash => $phash,
    }, $class;
}

sub i {
    my $this   = shift;
    my $symbol = shift;

    return $this->{phash}{$symbol};
}

sub g {
    my $this   = shift;
    my $symbol = shift;

    return $this->{elfh}->get_octet( @{ $this->i($symbol) }{qw(Value Size)} );
}

sub locate_symbol {
    my $this = shift;
    my $addr = shift;

    my $phash = $this->{phash};
    my $idx = _binary_search( $phash, 0, $#{ $phash->{yjlist} }, $addr );
    return $phash->{yjlist}[$idx];
}

package Runtime;

sub _get_translation_table {
    my $rdfh                   = shift;
    my $kernel_space_pagetable = 0x00124000
      ;    # this is kernel_space_pagetable f0024000 in l4 kernel. 2xdelta
    my @table;

    seek $rdfh, $kernel_space_pagetable, 0;
    read $rdfh, my $buf, 16 * 1024;
    @table = unpack( "L4096", $buf );
    return \@table;
}

sub new {
    my $class = shift;
    my $rd_fn = shift;

    open my $rdfh, "<", $rd_fn or die $!;
    binmode $rdfh;
    return bless { rdfh => $rdfh, }, $class unless @_;

    my $elf_fn = shift;

    my $elfh = Elf->new($elf_fn);
    my $symh = Sym->new($elfh);
    return bless {
        elfh     => $elfh,
        rdfh     => $rdfh,
        symh     => $symh,
        l1_table => _get_translation_table($rdfh),
    }, $class;
}

sub i {
    my $this   = shift;
    my $symbol = shift;
    return $this->{symh}->i($symbol);
}

sub g {
    my $this   = shift;
    my $symbol = shift;

    return ::file_get_chunk( $this->{rdfh},
        @{ $this->{symh}->i($symbol) }{qw(Value Size)} );
}

sub locate_symbol {
    my $this = shift;
    my $addr = shift;
    $this->{symh}->locate_symbol($addr);
}

sub vir2phy {
    my $this = shift;
    my $vir  = shift;

    return $vir if $vir < 0x08000000;
    my $l1_table       = $this->{l1_table};
    my $rdfh           = $this->{rdfh};
    my $l1_table_index = $vir >> 20;
    my $l2_table_index = ( $vir & ( ( 1 << 20 ) - 1 ) ) >> 12;

    #	my $page_index     = ($vir & ((1<<12) -1));
    my $l1_descriptor = $l1_table->[$l1_table_index];
    warn( "no l1 desc ", sprintf( "0x%08x", $vir ) . "!!!!" ), return undef
      unless $l1_descriptor;
    return ( $l1_descriptor & 0xfff00000 ) | ( $vir & 0x000fffff )
      if ( $l1_descriptor & 0b11 ) == 0b10;    # 2xdelta
    die sprintf( "%#b!!!", $l1_descriptor ) if ( $l1_descriptor & 0b11 ) != 1;

    #	$DB::single = 1;
    my $l2_table_off = $l1_descriptor & 0xfffffc00;
    if ( not exists $this->{l2_table}{$l2_table_off} ) {
        my $buf = ::file_get_chunk( $rdfh, $l2_table_off, 256 * 4 );
        my $l2_table = [ unpack( "L256", $buf ) ];
        $this->{l2_table}{$l2_table_off} = $l2_table;
    }
    my $l2_descriptor = $this->{l2_table}{$l2_table_off}[$l2_table_index];
    warn( "no l2 desc ",
        sprintf( "0x%08x 0x%08x", $vir, $l1_descriptor ) . "!!!!" ),
      return undef
      unless $l2_descriptor;

#	warn sprintf("0x%08x 0x%08x",$vir, $l1_descriptor)."!!!!" if ($l2_descriptor & 0b11) != 0b10; # 2xdelta
    return ( $l2_descriptor & 0xfffff000 ) | ( $vir & ( ( 1 << 12 ) - 1 ) )
      if ( $l2_descriptor & 0b11 ) == 0b10;    # small:
    return ( $l2_descriptor & 0xffff0000 ) | ( $vir & ( ( 1 << 16 ) - 1 ) )
      if ( $l2_descriptor & 0b11 ) ==
      0b01;    # large: may need to use l2_desc&0xffff0000 | $page_index
}

sub rget {
    my $this = shift;
    my $vir  = shift;
    my $size = shift;
    my $phy  = $vir < 0x08000000 ? $vir : $this->vir2phy($vir);
    return ::file_get_chunk( $this->{rdfh}, $phy, $size );
}

sub eget {
    my $this = shift;
    my $vir  = shift;
    my $size = shift;
    my $off  = $this->{elfh}->vir2off($vir);
    return $this->{elfh}->get_octet( $off, $size );
}

sub get_str {
    my $this = shift;
    my $vir  = shift;
    my $str = eval {$this->eget($vir,500)};
    $str = $this->rget($vir,500) if $@;
    return unpack "Z*", $str;
}

package main;

# TODO: add trace_buffer parsing mechanisms.
# related files: msg.c msg_save_trace()
# diagdebug.c diag_debug_trace_to_buffer()
# the trace_buffer size is 128K bytes and each record takes 6 bytes
# totally there can be over 16K records left in RAM.
# header:
#  b15~b13: MSG|EVT
#  b12~b08: nargs
#  b07~b04: details (byte_sized | savevars | savetime)
#  b03~b00: type DIAG_DEBUG_STANDARD|DIAG_DEBUG_QSHRINK
#
# MSG:
#  header:         2 bytes M
#  const type ptr: 4 bytes M
#  timestamp:      8 bytes
#  savevars:       num_args * x (x=0,1,2,3)
# EVT:
#  header:  2 bytes
#  evt_len: 2 bytes
#  events:  evt_len bytes
#
# Format of diag_debug_hdr_type:
#  Bits 15:13    Type Field (Event, Msg, etc.)
#  Bits 11:8     Number of arguments Field
#  Bits  7:4     Message Type Field (Standard MSG/Qshrink MSG)
#  Bits  3:0     Details Field
#                Bit 3:2 "Byte Sized Arguments" Field
#                Bit 1   Save Time flag
#                Bit 0   Save Vars flag
#
#msg_const_type:
#  msg_desc_type desc:		/* ss_mask, line, ss_id */
#   uint16 line;			/* Line number in source file */
#   uint16 ss_id;			/* Subsystem ID               */
#   uint32 ss_mask;		/* Subsystem Mask             */
#  const char *fmt;		/* Printf style format string */
#  const char *fname;		/* Pointer to source file name */
#  boolean do_save;              /* If TRUE, save msg to RAM buffer */

sub DIAG_DEBUG_GET_TYPE        { ( $_[0] >> 13 ) }
sub DIAG_DEBUG_MSG_NUM_ARGS    { ( ( $_[0] >> 8 ) & 0x1F ) }
sub DIAG_DEBUG_MSG_TYPE        { ( ( $_[0] >> 4 ) & 0xF ) }
sub DIAG_DEBUG_GET_DETAILS     { ( $_[0] & 0xF ) }
sub DIAG_DEBUG_MSG_BIT         { 0x1 }
sub DIAG_DEBUG_LOG_BIT         { 0x2 }
sub DIAG_DEBUG_EVT_BIT         { 0x4 }
sub DIAG_DEBUG_SAVETIME        { 0x2 }
sub DIAG_DEBUG_SAVEVARS        { 0x1 }
sub DIAG_DEBUG_BYTE_SIZED_ARGS { ( ( $_[0] & 0xC ) >> 2 ) }

sub gen_iter {
    my $p       = shift;
    my $pbuf    = shift;
    my $tb_size = shift;

    return sub {
        my $size = shift;
        my $ret;
        while ( $size-- ) {

#	    printf "iter: %08x %08x %08x %02x$/", $p, $size, $tb_size,unpack "C", substr($$pbuf,$p,1);
            $ret .= substr( $$pbuf, $p, 1 );
            $p = ( $p + 1 ) % $tb_size;
        }
        return $ret;
      }
}

# stolen from FormatT32F3Trace.pl
sub CompletePreviousItem
{
    my $item = shift;

    my $final_time = sprintf("%02d:%02d:%02d.%03d",
			     $item->{time_h},
			     $item->{time_m},
			     $item->{time_s},
			     $item->{time_ms});
    my $final_format = do {
	if (@{$item->{margs}}) {
	    sprintf($item->{mformat},@{$item->{margs}});
	} else {
	    $item->{mformat};
	}
    };
    my $final_msg = sprintf("%s    %5d   %s   %s",
			    $final_time,
			    $item->{mline},
			    $item->{mfile},
			    $final_format);
    return $final_msg;
}

# constants for use by Time conversion
my $max32bit = hex("FFFFFFFF");
my $cfactor = Math::BigInt->new($max32bit);
$cfactor = $cfactor+1;
sub ConvertTime
{
    my $item = shift;

    # Compute starting time from timestamp.
    # Need to use BigInt as this is a 48bit number
    my $time = $item->{time_high16} * $cfactor + $item->{time_low32};

    # Timestamp is in 1.25ms units, so convert to actual ms
    $time = ($time*5)/4;			
    
    # time starting in ms units
    # extract miliseconds value
    $item->{time_ms} = $time % 1000;
    $time = ($time - $item->{time_ms})/1000;

    # time now in seconds
    # extract seconds value
    $item->{time_s} = $time % 60;
    $time = ($time - $item->{time_s})/60;

    # time now in minutes
    # extract minutes value
    $item->{time_m} = $time % 60;
    $time = ($time - $item->{time_m})/60;

    # time now in hours
    # extract hours value
    $item->{time_h} = $time % 24;

    return $item;
}

sub dump_amss_trace_buffer {
    my $rt     = shift;
    my $tb_addr   = shift;
    my $tb_size   = shift;
    my $tb_head   = shift;
    my $tb_tail   = shift;
    my $tb_count  = shift;
    my $qhash     = shift;
    my $fho       = shift;

#    printf {$fho} sprintf("!!!!0x%08x 0x%08x 0x%08x", $tb_addr, $tb_size, $tb_head);
#    print $/;
    my $buf = $rt->rget($tb_addr, $tb_size);
    my $p = $tb_tail;
    my $iter = gen_iter( $tb_tail, \$buf, $tb_size );

    while ( $tb_count-- ) {

        #	my ($header, $value) = unpack "vV", substr($buf, $p, 6);
        my $header = unpack "v", $iter->(2);

#	print {$fho} sprintf("%016b nargs=%d byte_sized=%d", $header, DIAG_DEBUG_MSG_NUM_ARGS($header), DIAG_DEBUG_BYTE_SIZED_ARGS($header)), " ";
        my $type = DIAG_DEBUG_GET_TYPE($header);
        if ( $type == DIAG_DEBUG_MSG_BIT() ) {
	    my $timeh;
            my @args;
            my ( $line, $ss_id, $ss_mask, $fmt, $fname, $do_save, $hash, $filename, $format );
#            print {$fho} "MSG ";
            my $addr = unpack "L", $iter->(4);
	    if (DIAG_DEBUG_MSG_TYPE($header)) {
		if ( $addr < 0x08000000) {
		( $line, $ss_id, $ss_mask, $hash ) =
		    unpack "SSLL", $rt->rget( $addr, 12 );
		} else {
			( $line, $ss_id, $ss_mask, $hash ) =
				unpack "SSLL", $rt->eget( $addr, 12 ); 
		}
		($filename, $format) = @{$qhash->{$hash}} if exists $qhash->{$hash};
	    } else {
		( $line, $ss_id, $ss_mask, $fmt, $fname, $do_save ) =
		    unpack "SSLLLL", $rt->rget( $addr, 20 );
	    }
            my $details = DIAG_DEBUG_GET_DETAILS($header);
            if ( $details & DIAG_DEBUG_SAVETIME() ) {

                #		print {$fho} "SAVETIME";
                my ( $timestamp, $t1 ) = unpack "LS", $iter->(6);
		$timeh = ConvertTime( {
		    time_high16 => $t1,
		    time_low32 => $timestamp,
		} );

                #		print {$fho} sprintf("0x%08x 0x%08x ", $timestamp, $t1);
#                print {$fho} $timestamp + $t1 * ( 0xffffffff + 1 ), " ";
            }
            if ( $details & DIAG_DEBUG_SAVEVARS ) {

                #		print {$fho} "SAVEVARS";
                my $byte_sized = DIAG_DEBUG_BYTE_SIZED_ARGS($header);
                my $nargs      = DIAG_DEBUG_MSG_NUM_ARGS($header);
                my $len        = $nargs * ( 4 - $byte_sized );

       #		print "byte_sized=$byte_sized,len=$len";
       #		print {$fho} sprintf("%02x", $_) for (unpack "C"x$len, $iter->($len));
                if ( $len > 0 ) {
                    my $arg = $iter->($len);
                    @args = ( unpack "L" x $nargs, $arg ) if $byte_sized == 0;
                    @args = ( unpack "S" x $nargs, $arg ) if $byte_sized == 2;
                    @args = ( unpack "C" x $nargs, $arg ) if $byte_sized == 3;
                    if ( $byte_sized == 1 ) {
                        my @octets = unpack "C" x $len, $arg;
                        while (@octets) {
                            push @args,
                              $octets[0] +
                              $octets[1] * 256 +
                              $octets[2] * 256 * 256;
                            shift @octets;
                            shift @octets;
                            shift @octets;
                        }
                    }
                }
            }
            $format = $rt->get_str($fmt) unless DIAG_DEBUG_MSG_TYPE($header);
	    $format = $format || '';
=comment
            if ( $format =~ /%s/ ) {

                #		print $format, "^&^&";
                my $addr = shift @args;
                my $str  = $rt->get_str($addr) || '';
                unshift @args, $str;    #."%ss%";
            }
=cut
           $format =~ s/\%p/%x/g;
	    $filename = $rt->get_str($fname) unless DIAG_DEBUG_MSG_TYPE($header);
	    $filename = $filename || '';
	    print {$fho} CompletePreviousItem( {
		mline => $line,
		mfile => $filename,
		mformat => $format,
		margs => \@args,
		time_ms => $timeh->{time_ms},
		time_s => $timeh->{time_s},
		time_m => $timeh->{time_m},
		time_h => $timeh->{time_h},
	    } );
#           print {$fho} $filename, " $line ";
#	    use MIME::QuotedPrint ();
#	    $format = MIME::QuotedPrint::encode($format);
#	    if (@args) {
#		printf {$fho} $format, @args;
#	    } else {
#		print {$fho} $format;
#	    }
#	    print {$fho} "[".scalar @args."]"."@args";
        }
        elsif ( $type == DIAG_DEBUG_EVT_BIT() ) {
            print {$fho} "EVT";
            my $evt_len = unpack "S", $iter->(2);

            #	    my $evt_len = unpack "C", substr($buf, $p, 1);
            print {$fho} sprintf( "%02x", $_ )
              for ( unpack "C" x $evt_len, $iter->($evt_len) );
        }
        elsif ( $type == DIAG_DEBUG_LOG_BIT() ) {
            die "";
        }
        else {
            die "";
        }
        print {$fho} $/;
    }
}

sub RUNNABLE_STATE { ( ( $_[0] << 1 ) | 0 ) }
sub BLOCKED_STATE  { ( ( $_[0] << 1 ) | 1 ) }
my %thread_state = (
    RUNNABLE_STATE(1)                => "running",
    RUNNABLE_STATE(2)                => "retrying_mutex",
    BLOCKED_STATE( 0xffffffff >> 1 ) => "waiting_forever",
    BLOCKED_STATE(2)                 => "waiting_notify",
    BLOCKED_STATE(5)                 => "polling",
    BLOCKED_STATE(6)                 => "halted",
    BLOCKED_STATE(7)                 => "aborted",
    BLOCKED_STATE(8)                 => "xcpu_waiting_deltcb",
    BLOCKED_STATE(12)                => "xcpu_waiting_exregs",
    BLOCKED_STATE(13)                => "waiting_mutex",
);

my @l1_addr_bits = ( 0, 22,    12,   20 );
my @l2_addr_bits = ( 0, 16,    20,   22 );
my @l1_type      = qw(fault coarse section fine);
my @l2_type      = qw(fault large small tiny);
my @l2_offset    = ( 0, 65536, 1024, 0 );    # fixme

sub unique_via_slice {
    my %uniq;
    @uniq{@_} = ();
    return keys %uniq;
}

sub l1_range {
    my $desc = shift;

    my $type = $desc & 3;
    return ( $desc & 0xfff00000, ( $desc & 0xfff00000 ) + 0xfffff )
      if $type == 0b10;    # section
    return ( $desc & 0xfffffc00, ( $desc & 0xfffffc00 ) + 0x3ff )
      if $type == 0b01;    # coarse
}

sub l2_range {
    my $desc = shift;

    my $type = $desc & 3;
    return ( $desc & 0xffff0000, ( $desc & 0xffff0000 ) + 0xffff )
      if $type == 0b01;    # large
    return ( $desc & 0xfffff000, ( $desc & 0xfffff000 ) + 0xfff )
      if $type == 0b10;    # small
    return ( $desc & 0xfffffc00, ( $desc & 0xfffffc00 ) + 0x3ff )
      if $type == 0b11;    # tiny
}

sub do_print_address_table {
    my $fh  = shift;
    my $fho = shift;

    my $tmp      = rd_get_translation_table($fh);
    my $l1_table = $tmp->{l1_table};

    my $i = -1;
    foreach ( @{$l1_table} ) {
        $i++;
        next if ( $_ & 3 ) == 0;
        printf( "0x%03xXXXXX ", $i ),
          printf( "0x%08x 0x%08x~0x%08x %02b %10s$/",
            $_, l1_range($_), $_ & 3, $l1_type[ $_ & 3 ] ),
          next
          unless ( $_ & 3 ) == 1;
        my $l2_table = $_ & 0xfffffc00;
        my $l1_desc  = $_;
        seek $fh, $l2_table, 0;
        read $fh, my ($buf), 1024;
        my @table = unpack( "L256", $buf );

        my $j      = -1;
        my $offset = 0;
        my $phy    = $i * 2**20 - 4096;
        foreach (@table) {
            $phy += 4096;
            $j++;
            next if ( $_ & 3 ) == 0;
            next if ( $_ & 3 ) == 1 and ( $j % 16 ) != 0;
            printf( "0x%08x ", $phy ),
              printf(
                "0x%08x 0x%08x~0x%08x %02b %10s ",
                $l1_desc,     l1_range($l1_desc),
                $l1_desc & 3, $l1_type[ $l1_desc & 3 ]
              );
            printf( "0x%08x 0x%08x~0x%08x %02b %s$/",
                $_, l2_range($_), $_ & 3, $l2_type[ $_ & 3 ] );
        }
    }
}

sub get_trace_buffer_part {
    my $h_trace_buffer = shift;
    my $sub_tb         = shift;
    my $sub_tb_head    = shift;

    my $p = 0;
    while () {
        last if ( $p + 4 * 6 ) > length($sub_tb);

        #		my $value = unpack "L", substr($sub_tb, $p, 4);
        #		$h_trace_buffer->{$value} = $p + $sub_tb_head;
        my ( $timestamp_low, $timestamp_hi, $flags, $from_ktcb, $to_ktcb, $tid )
          = unpack "LLLLLL", substr( $sub_tb, $p, 4 * 6 );
        push @{$h_trace_buffer},
          {
            timestamp => $timestamp_low,
            flags     => $flags,
            from      => $from_ktcb,
            to        => $to_ktcb,
            tid       => $tid,
            offset    => $p + $sub_tb_head,
          };
        $p += 4 * 6;

        #		printf "p=%08x, sub_tb_head=%08x$/", $p, $sub_tb_head;
    }
}

sub rd_get_trace_buffer {
    my $rt    = shift;
    my $khash = shift;
    my $fho   = shift;

    ( my $ktcbh, my $tidh ) = ( $khash->{ktcbh}, $khash->{tidh} );

    my $trace_buffer_sym =
      0xf001e64c;    # this is trace_buffer f001e64c in l4 kernel. 2xdelta
    my $buf = $rt->rget( $trace_buffer_sym, 4 );
    my $trace_buffer_off = unpack "L", $buf;

    #    printf "tboff = 0x%08x$/", $trace_buffer_off;
    my $trace_buffer = $rt->rget( $trace_buffer_off, 0x1000 );
    my ( $buf_size, $buf_off1, $buf_off2, $buf_head1, $buf_head2 ) =
      unpack "LLLLL", substr( $trace_buffer, 28, 5 * 4 );
    my @list;
    get_trace_buffer_part( \@list,
        substr( $trace_buffer, $buf_off1, $buf_size ), $buf_off1 );
    get_trace_buffer_part( \@list,
        substr( $trace_buffer, $buf_off2, $buf_size ), $buf_off2 );

    my @sorted = sort { $b->{timestamp} <=> $a->{timestamp} } @list;

    #	print scalar @sorted, "!!!\n";
    #	printf "%08x###$/", $sorted[167]{timestamp};
    my $p = shift @sorted;
    print {$fho} "Index Timestamp Ticks Event         Data...\n";
    print {$fho} "-" x 70, $/;

    #	$DB::single = 1;
    printf {$fho} "current -------- --- Thread Switch %08x %s %08x$/",
      $p->{tid}, pack( "A16", $ktcbh->{ $p->{tid} }{name} ), $p->{to};
    my $timestamp = $p->{timestamp};
    my $index     = 167;
    my $ticks     = $p->{timestamp} - $sorted[0]{timestamp};
    my $lastp;
    while ( $p = shift @sorted ) {
        printf {$fho} "  %3d   %08x %3d Thread Switch %08x %s %08x$/", $index--,
          $timestamp, $ticks, $p->{tid},
          pack( "A16", $ktcbh->{ $p->{tid} }{name} ), $p->{to};
        $timestamp = $p->{timestamp};
        $ticks = $p->{timestamp} - $sorted[0]{timestamp} if ( scalar @sorted );
        $lastp = $p;
    }
    my $tid = $tidh->{ $lastp->{from} };
    printf {$fho} "  %3d   %08x --- Thread Switch %08x %s %08x$/", 0,
      $timestamp, $tid, pack( "A16", $ktcbh->{$tid}{name} ), $lastp->{from};

 #	print $p->{timestamp},"!!!\n";
 #	for (sort {$b->[0] <=> $a->[0]} @list) {
 #		printf "%08x %08x %08x %08x\n", $_->[0], $_->[1][1], $_->[1][2], $_->[1][3];
 #	}
}

sub rd_get_tid {
    my $rt = shift;

    my $tid;
    my $buf = $rt->g('qxdm_dbg_msg') . $rt->g('cci_ex_log_info');
    if ( $buf =~ /tid=([0-9a-f]+)/ ) {
        $tid = hex($1);
    }
    else {

        #	print STDERR "qxdm_dbg_msg=$buf has no tid! use cciui tid!\n";
        $tid = undef;
    }
    return $tid;
}

sub rd_get_dog_task {
    my $rt = shift;

    my $buf = unpack "Z*", $rt->g('cci_ex_log_info');
    if ( $buf =~ /dog:\s*(\S+)/ ) {
        return $1;
    }
    else {
        return;
    }
}

sub rd_get_console {
    my $rt = shift;

    my $text = $rt->rget( 0xf0021ae8, 2048 )
      ;   # mapping to jtag_console_buffer 0xf0021ae8 in l4kernel's map. 2xdelta
    return unpack "Z*", $text;
}

sub get_one_ktcb {
    my $buf   = shift;

    my $dbg_name_off = 0x114;    # 2xdelta
    my $context_off  = 0x50;     # 2xdelta
    my $state_off    = 0x24;     # 2xdelta
#    my $t_next_off   = 0x10c;    # 2xdelta
#    my $t_prev_off   = 0x110;    # 2xdelta
    my $t_next_off   = 0xb8+7*4;    # 2xdelta
    my $t_prev_off   = 0xb8+8*4;    # 2xdelta
    my $priority_off = 0xb0;     # 2xdelta, 176 in decimal
#    my $list_off     = 0xb8;	 # 2xdelta
    my $utcb_off     = 8;        # 2xdelta

    my $tid = unpack( "L", substr( $buf, 0, 4 ) );    # thread id
    return unless $tid;
    my $utcb = unpack( "L", substr( $buf, $utcb_off, 4 ) );      # utcb
    return unless $utcb;
    my $priority = unpack( "L", substr( $buf, $priority_off, 4 ) );
    return unless $priority;
#    return if $priority > 255;
    my $state = unpack( "L", substr( $buf, $state_off, 4 ) );    # state
    return unless defined $thread_state{$state};

    my $name = substr( $buf, $dbg_name_off, 16 );
            #	$DB::single = 1 if $tid == 0;
    my $p = 0;
    while ($p < 16) {
	my $c = substr($name, $p++, 1);
	last if $c eq "\0";
	return if ord($c) > 127;
	return if ord($c) < ord(' ');
    }
    return if $p == 1;
    $name = substr($name, 0, $p-1);

    my (
        $klr, $r0, $r1,  $r2,  $r3,  $r4, $r5, $r6, $r7,
        $r8,  $r9, $r10, $r11, $r12, $sp, $lr, $pc, $cpsr
    ) = unpack( "L18", substr( $buf, $context_off, 4 * 18 ) );

    my $t_next   = unpack( "L", substr( $buf, $t_next_off,   4 ) );
    my $t_prev   = unpack( "L", substr( $buf, $t_prev_off,   4 ) );
#    my @lists    = unpack( "L9",substr( $buf, $list_off,     4*9));
    my %hash = (
	name     => $name,
	utcb     => $utcb,
	state    => $state,
	pc       => $pc,
	sp       => $sp,
	lr       => $lr,
	cpsr     => $cpsr,
	t_next   => $t_next,
	t_prev   => $t_prev,
	priority => $priority,
	klr      => $klr,
	r0       => $r0,
	r1       => $r1,
	r2       => $r2,
	r3       => $r3,
	r4       => $r4,
	r5       => $r5,
	r6       => $r6,
	r7       => $r7,
	r8       => $r8,
	r9       => $r9,
	r10      => $r10,
	r11      => $r11,
	r12      => $r12,
    );
 #   $ktcbh->{$tid}{lists}    = \@lists;
    return ($tid, \%hash, $t_prev, $t_next);
}

sub rd_get_ktcb {
    my $rt = shift;

    my $ktcbh = {};
    my $tidh  = {};
    my @queue;
    my ($p, $tid, $onektcb, $prev, $next);

    my $global_present_list_sym = 0xf001c980; # 2xdelta
    my $buf = $rt->rget( $global_present_list_sym, 4 );
    my $global_present_list = unpack "L", $buf;

    push @queue, $global_present_list;
    while (my $ktcb = shift @queue) {
	$p = $rt->vir2phy($ktcb);
	($tid, $onektcb, $prev, $next) = get_one_ktcb( $rt->rget( $p, 0x170 ) );    # 2xdelta
	$ktcbh->{$tid} = $onektcb;
	my $user_defined_handle = unpack "L",
	    $rt->rget( $ktcbh->{$tid}{utcb} + 4, 4 );
	my $stack_limit = unpack "L", $rt->rget( $user_defined_handle + 16, 4 );
	$ktcbh->{$tid}{ktcb}        = $ktcb;
	$ktcbh->{$tid}{phys}        = $p;
	$ktcbh->{$tid}{stack_limit} = $stack_limit;
	$tidh->{$ktcb}              = $tid;
	push(@queue, $prev) unless exists $tidh->{$prev};
	push(@queue, $next) unless exists $tidh->{$next};
    }
    return { ktcbh => $ktcbh, tidh => $tidh };
}

sub get_running_tids {
    my $khash = shift;

    ( my $ktcbh, my $tidh ) = ( $khash->{ktcbh}, $khash->{tidh} );
    return grep {
             ( $ktcbh->{$_}{state} == RUNNABLE_STATE(1) )
          && ( $ktcbh->{$_}{name} ne 'idle' )
    } keys %{$ktcbh};

    #    return keys %{$ktcbh};
    #    return grep {$ktcbh->{$_}{name} !~ /^(IRQ|FIQ)/} keys %{$ktcbh};
}

sub get_tid_from_name {
    my $khash = shift;
    my $name  = shift;

    ( my $ktcbh, my $tidh ) = ( $khash->{ktcbh}, $khash->{tidh} );
    return grep { $ktcbh->{$_}{name} eq $name } keys %{$ktcbh};
}

sub print_ktcb {
    my $khash = shift;
    my $fho   = shift;

    ( my $ktcbh, my $tidh ) = ( $khash->{ktcbh}, $khash->{tidh} );
    print {$fho} "-" x 145, $/;
    print {$fho} "L4 Thread List\n" . "-" x 145, $/;
    print {$fho} pack "A9A9A9A16A9A9A9A4A9A9A9A9A9A9A9A9",
      qw(ktcb thrd_id state state_name sp lr pc pri r0 r1 r2 r3 r4 stack_lm utcb name);
    print {$fho} $/;
    print {$fho} "-" x 145, $/;

    #	$DB::single = 1;
    my @tidlist =
	sort {
	    $ktcbh->{$b}{priority} <=> $ktcbh->{$a}{priority} ||
	    $ktcbh->{$a}{ktcb}     <=> $ktcbh->{$b}{ktcb}
	    } keys %{$ktcbh};

    foreach my $tid (@tidlist) {
        printf {$fho} (
"%08x %08x %08x %s %08x %08x %08x %03d %08x %08x %08x %08x %08x %08x %08x ",
            $ktcbh->{$tid}{ktcb},
            $tid,
            $ktcbh->{$tid}{state},
            pack( "A15", $thread_state{ $ktcbh->{$tid}{state} } ),
            $ktcbh->{$tid}{sp},
            $ktcbh->{$tid}{lr},
            $ktcbh->{$tid}{pc},
            $ktcbh->{$tid}{priority},
            $ktcbh->{$tid}{r0},
            $ktcbh->{$tid}{r1},
            $ktcbh->{$tid}{r2},
            $ktcbh->{$tid}{r3},
            $ktcbh->{$tid}{r4},
            $ktcbh->{$tid}{stack_limit},
            $ktcbh->{$tid}{utcb},
#            $ktcbh->{$tid}{t_next},
#            $ktcbh->{$tid}{t_prev},
        );
        print {$fho} $ktcbh->{$tid}{name}, $/;
    }
}

sub get_image_data {
    my $rt      = shift;
    my $address = shift;
    my $width   = shift;
    my $height  = shift;

    #	print "addr=$address\n";
    my $img = $rt->rget( $address, $width * $height * 2 );

#	print "len=",bytes::length($img),$/;
#    die "$!" if length($img) != $width*$height*2; # comment out assert for perl 5.6 maybe dangerous.
    my $d = "";
    my $p = 0;
    for ( 0 .. $height - 1 ) {
        my $l;
        for my $n ( 0 .. $width - 1 ) {
            my ( $r, $g, $b, $pixel );
            $pixel = unpack( "S", substr( $img, $p, 2 ) );
            $r = ( $pixel / 2**11 ) * ( 2**3 );
            $g = ( ( $pixel % 2**11 ) / ( 2**5 ) ) * ( 2**2 );
            $b = ( $pixel % 2**5 ) * ( 2**3 );
            $l .= pack( "CCCC", int($b), int($g), int($r), 0 );
            $p += 2;
        }
        $d = $l . $d;
    }
    return $d;
}

sub dump_frame_buffer {
    my $rt      = shift;
    my $lcd_buf = shift;
    my $width   = shift;
    my $height  = shift;
    my $bmp_fn  = shift;

    my $bfSize     = $width * $height * 4 + 54;
    my $bfOffBits  = 54;
    my $biSize     = 40;
    my $biPlanes   = 1;
    my $biBitCount = 32;

    my $bmpHeader = "BM" . pack( "LLL", $bfSize, 0, $bfOffBits );
    my $bmpInfo = pack( "LLLSSLLLLLL",
        $biSize, $width, $height, $biPlanes, $biBitCount, 0, 0, 0, 0, 0, 0 );
    my $bmpData = get_image_data( $rt, $lcd_buf, $width, $height );
    open my $fh, ">", $bmp_fn or die "$bmp_fn: $!\n";
    binmode $fh;
    print $fh $bmpHeader . $bmpInfo . $bmpData;
    close $fh;
}

sub dump_stack {
    my $rt    = shift;
    my $khash = shift;
    my $tid   = shift;
    my $fho   = shift;

    ( my $ktcbh, my $tidh ) = ( $khash->{ktcbh}, $khash->{tidh} );
    my $taskh = $ktcbh->{$tid};
    my $pc    = $taskh->{pc};
    my $sp    = $taskh->{sp};
    return unless $sp < 0x08000000;
    my $cpsr = $taskh->{cpsr};

    print {$fho} "-" x 70, $/;
    print {$fho} "Call stack of task ", $taskh->{name}, $/;
    print {$fho} "-" x 70, $/;

    my $spsym = $rt->locate_symbol($sp);

    #    my $stack_start = $rt->i($spsym)->{Value};
    my $stack_start = $taskh->{stack_limit};

    #    my $stack_size  = $rt->i($spsym)->{Size};
    my $bottom_limit = $rt->i($spsym)->{Value} + $rt->i($spsym)->{Size};

    my %regsymh;
    for my $reg (qw(klr r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 lr pc)) {
        next unless $taskh->{$reg};
        my $regsym = $rt->locate_symbol( $taskh->{$reg} );
	$regsymh{$reg} = $regsym;
        printf {$fho} "%s: 0x%08x %s + 0x%08x", pack( "A3", $reg ),
          $taskh->{$reg}, pack( "A50", $regsym ),
          $taskh->{$reg} - $rt->i($regsym)->{Value};
        print {$fho} $/;
    }

    ## get stack info
    #    my $stack_used = $stack_start + $rt->i($spsym)->{Size} - $sp;

    my $symbol = $regsymh{pc};
    my $p      = $sp;
    while ( $symbol ne '__thread_stub' ) {
        my $value = unpack( "L", $rt->rget( $p, 4 ) );
        if ( $value > 0x1000 ) {
            $symbol = $rt->locate_symbol($value);
            my $off = $value - $rt->i($symbol)->{Value};
            my $str = "";
            if ( $rt->i($symbol)->{Type} eq 'OBJECT' ) {
            }
            elsif ( $rt->i($symbol)->{Type} eq 'FUNC' ) {
                printf {$fho} "0x%08x 0x%08x %8d %8d %s\n",
                  $p, $value, $off, $rt->i($symbol)->{Size},
                  pack( "A7A21A40", $rt->i($symbol)->{Type}, $str, $symbol );
            }
        }
        else {

            #			printf "0x%08x 0x%08x %8d\n", $p+$sp, $value, $value;
        }
        $p += 4;
        last if $p >= $bottom_limit;
    }
    my $stack_size = $p - $stack_start;

#    printf {$fho} "stack bottom=0x%08x\n", $stack_start+$rt->i($spsym)->{Size};
    printf {$fho} "stack bottom=0x%08x\n", $p;
    printf {$fho} "#sp: 0x%08x %s + 0x%08x %d/%d = %d" . "%% left\n",
      $sp, $spsym, $sp - $stack_start, $sp - $stack_start, $stack_size,
      ( $stack_size == 0 )
      ? 0
      : int( ( $sp - $stack_start ) * 100 / $stack_size );
}

sub do_rd {
    my $rt    = shift;
    my $khash = shift;
    my $fho   = shift;

    my $consoleout = rd_get_console($rt);
    print {$fho} "-" x 70, $/, "L4 Console\n" . "-" x 70, $/;
    print {$fho} $consoleout, $/;
    print {$fho} "-" x 70, $/, "L4 Trace Buffer\n" . "-" x 70, $/;
    rd_get_trace_buffer( $rt, $khash, $fho );
}

sub do_call_stack {
    my $rt      = shift;
    my $khash   = shift;
    my $r_tasks = shift;
    my $fho     = shift;

    my $tid;
    my @tids;
    if ( defined( $tid = rd_get_tid($rt) ) ) {
        printf {$fho} "#tid: 0x%08x\n", $tid;
        push @tids, $tid;
    }
    if ( my $dog = rd_get_dog_task($rt) ) {
        push @tids, get_tid_from_name( $khash, $dog );
    }
    push @tids, get_tid_from_name( $khash, "CCIUI" );
    push @tids, get_tid_from_name( $khash, "Main Task" );
    push @tids, $_ foreach map { get_tid_from_name( $khash, $_ ) } @{$r_tasks};

    dump_stack( $rt, $khash, $_, $fho )
      foreach sort { $a <=> $b }
      unique_via_slice( @tids, get_running_tids($khash) );
}

sub get_info_pos {
    my $ret = [];
    while (<DATA>) {
        chomp;
        my ( $key, $addr ) = split /\s+/, $_;

        #	$ret->{$key} = hex($addr);
        push @{$ret}, [ $key, hex($addr) ];
    }
    return $ret;
}

sub rd_get_info {
    my $rt   = shift;
    my $hint = shift;

    my $ret = {};
    for ( @{$hint} ) {
        my ( $key, $addr ) = @{$_};
        my $buf = $rt->rget( $addr, 0x100 );
        $ret->{$key} = unpack "Z*", $buf;
    }
    return $ret;
}

sub elf_get_info {
    my $rt   = shift;
    my $hint = shift;

    my $ret = {};
    for ( @{$hint} ) {
        my ( $key, $vir ) = @{$_};
        my $buf = $rt->eget( $vir, 0x100 );

        #	printf("%08x %08x$/", $vir, $off);
        $ret->{$key} = unpack "Z*", $buf;
    }
    return $ret;
}

sub do_g_asMonitorHdr {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('g_asMonitorHdr');
    print {$fho} "-" x 40, "contents of g_asMonitorHdr$/";
    my $size           = $rt->i('g_asMonitorHdr')->{Size};
    my $g_asMonitorHdr = $rt->g('g_asMonitorHdr');
    my $p              = 0;
    while ( $p < $size ) {
        my ( $nAddr, $nAllocSize, $fnp, $lineNum ) = unpack "LLLL",
          substr( $g_asMonitorHdr, $p, 4 * 4 );
        my $filename = unpack "Z*", $rt->rget( $fnp, 100 );
        $p += 4 * 4;
        next unless $nAllocSize > 0;
        printf {$fho} "0x%08x %010d 0x%08x %s %d$/", $nAddr, $nAllocSize, $fnp,
          $filename, $lineNum;
    }
}

sub do_memPoolInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('memPoolInfo');
    print {$fho} "-" x 40, "contents of memPoolInfo$/";
    my $size        = $rt->i('memPoolInfo')->{Size};
    my $memPoolInfo = $rt->g('memPoolInfo');
    my $p           = 0;
    while ( $p < $size ) {
        my ( $fnp, $lineNum, $nAddr, $nAllocSize ) = unpack "LLLL",
          substr( $memPoolInfo, $p, 4 * 4 );
        my $filename = unpack "Z*", $rt->rget( $fnp, 100 );
        $p += 4 * 4;
        next unless $nAllocSize > 0;
        printf {$fho} "0x%08x %010d 0x%08x %s %d$/", $nAddr, $nAllocSize, $fnp,
          $filename, $lineNum;
    }
}

sub do_OEMHeapInfo {
    my $rt  = shift;
    my $fho = shift;

    if ($rt->i('OEMHeapInfoPtr'))
    {
        print {$fho} "-" x 40, "contents of OEMHeapInfo$/";
        my $OEMHeapInfoPtr = $rt->g('OEMHeapInfoPtr');
        my ( $pHeader ) = unpack "L",
              substr( $OEMHeapInfoPtr, 0, 4 );
        my $currentItem = $pHeader;
        
        while ( $currentItem != 0x00000000 ) 
        {
            my $buffer = $rt->rget($currentItem, 4*4);
            my ( $prevItem, $lr, $nSize, $nextItem ) 
            = unpack "LLLL", substr( $buffer, 0, 4*4 );

            my $lrpsym = $rt->locate_symbol($lr);
            printf {$fho} "0x%08x %010d 0x%08x %s$/", ($currentItem + 16), $nSize, $lr,
              $lrpsym;

            $currentItem = $nextItem;
            if ( $currentItem == $pHeader )
            {
                $currentItem = 0x00000000;
            }
        }
    }
    elsif ($rt->i('OEMHeapInfo'))
    {
        print {$fho} "-" x 40, "contents of OEMHeapInfo$/";
        my $size        = $rt->i('OEMHeapInfo')->{Size};
        my $OEMHeapInfo = $rt->g('OEMHeapInfo');
        my $p           = 0;
        while ( $p < $size ) {
            my ( $lrp, $nAddr, $nAllocSize ) = unpack "LLL",
              substr( $OEMHeapInfo, $p, 4 * 3 );
            my $lrpsym = $rt->locate_symbol($lrp);
            $p += 4 * 3;
            next unless $nAllocSize > 0;
            printf {$fho} "0x%08x %010d 0x%08x %s$/", $nAddr, $nAllocSize, $lrp,
              $lrpsym;
        }
    }

    return unless $rt->i('nAEEMaxFreeSize@q_malloc_1');
    my $nAEEMaxFreeSize = unpack "L", $rt->g('nAEEMaxFreeSize@q_malloc_1');    
    print {$fho} "nAEEMaxFreeSize::$nAEEMaxFreeSize$/";
}

sub do_JkCallerInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('JkCallerInfo');
    print {$fho} "-" x 40, "contents of JkCallerInfo$/";
    my $size        = $rt->i('JkCallerInfo')->{Size};
    my $JkCallerInfo = $rt->g('JkCallerInfo');
    my $p           = 0;
    while ( $p < $size ) {
        my ( $lrp, $nAddr, $nAllocSize ) = unpack "LLL",
          substr( $JkCallerInfo, $p, 4 * 3 );
        my $lrpsym = $rt->locate_symbol($lrp);
        $p += 4 * 3;
        next unless $nAllocSize > 0;
        printf {$fho} "0x%08x %010d 0x%08x %s$/", $nAddr, $nAllocSize, $lrp,
          $lrpsym;
    }
}

sub do_g_DumpMFWHeapInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    print {$fho} "-" x 80, "$/";
    print {$fho} "DumpMFWHeapInfo$/";
    print {$fho} "-" x 80, "$/";
    my $gCCI_MFW_MbCrtl = $rt->g('gCCI_MFW_MbCrtl');
    my $p = 4;
    my ( $pHeader ) = unpack "L",
          substr( $gCCI_MFW_MbCrtl, $p, 4 );
    my $currentItem = $pHeader;

    while( $currentItem != 0x00000000 )
    {
        my $buffer = $rt->rget($currentItem, 4*7);
        my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
        = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );

        if ( $poolNext == 0x00000000 )
        {
            my $fnp = unpack "Z*", $rt->rget( $filename, 20 );
            my $lrpsym = $rt->locate_symbol($lr);
            printf {$fho} "0x%08x\t\t%5d\t\t%20s\t\t%5d\t\t%s$/"
                , ($currentItem + 28), $nSize, $fnp, $nline, $lrpsym;
        }

        $currentItem = $nextItem;
        if ( $currentItem == $pHeader )
        {
            $currentItem = 0x00000000;
        }
    }
}

sub do_g_DumpCCIHeapInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    print {$fho} "-" x 80, "$/";
    print {$fho} "DumpSYSHeapInfo$/";
    print {$fho} "-" x 80, "$/";
    my $gCCIMM_SYS_MbCrtl = $rt->g('gCCIMM_SYS_MbCrtl');
    my $p = 4;
    my ( $pHeader ) = unpack "L",
          substr( $gCCIMM_SYS_MbCrtl, $p, 4 );
    my $currentItem = $pHeader;

    while( $currentItem != 0x00000000 )
    {
        my $buffer = $rt->rget($currentItem, 4*7);
        my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
        = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );

        if ( $poolNext == 0x00000000 )
        {
            my $fnp = unpack "Z*", $rt->rget( $filename, 20 );
            my $lrpsym = $rt->locate_symbol($lr);
            printf {$fho} "0x%08x\t\t%5d\t\t%20s\t\t%5d\t\t%s$/"
                , ($currentItem + 28), $nSize, $fnp, $nline, $lrpsym;
        }

        $currentItem = $nextItem;
        if ( $currentItem == $pHeader )
        {
            $currentItem = 0x00000000;
        }
    }
}

sub do_g_DumpGPFHeapInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    print {$fho} "-" x 80, "$/";
    print {$fho} "DumpGPFHeapInfo$/";
    print {$fho} "-" x 80, "$/";
    my $gCCI_GPF_MbCrtl = $rt->g('gCCI_GPF_MbCrtl');
    my $p = 4;
    my ( $pHeader ) = unpack "L",
          substr( $gCCI_GPF_MbCrtl, $p, 4 );
    my $currentItem = $pHeader;

    while( $currentItem != 0x00000000 )
    {
        my $buffer = $rt->rget($currentItem, 4*7);
        my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
        = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );

        if ( $poolNext == 0x00000000 )
        {
            my $fnp = unpack "Z*", $rt->rget( $filename, 20 );
            my $lrpsym = $rt->locate_symbol($lr);
            printf {$fho} "0x%08x\t\t%5d\t\t%20s\t\t%5d\t\t%s$/"
                , ($currentItem + 28), $nSize, $fnp, $nline, $lrpsym;
        }

        $currentItem = $nextItem;
        if ( $currentItem == $pHeader )
        {
            $currentItem = 0x00000000;
        }
    }
}

sub do_Timetick_Info{
    my $rt = shift;
    my $fho = shift;

    return unless $rt->i('parse_os_time');
    print {$fho} "-"x145,$/;
    print {$fho} "contents of Timetick Info$/";
    print {$fho} "-"x145,$/;
    my $parse_os_time = $rt->g('parse_os_time');
    my $parse_os_tick = $rt->g('parse_os_tick');
    my $parse_timetick64 = $rt->g('parse_timetick64');
    
    my ($os_time) = unpack "L", substr($parse_os_time, 0, 4);
    my ($os__min_time) = $os_time/(1000*60);
    my ($os_tick) = unpack "L", substr($parse_os_tick, 0, 4);
    my ($lo, $hi) = unpack "LL", substr( $parse_timetick64, 0, 8 );
    my $timetick64 = $lo+$hi*2**32;

    
    printf "parse_os_time = %u ms = %u min\n" , $os_time , $os__min_time;
    printf "parse_os_tick = %u tick\n" , $os_tick ;
    printf "parse_timetick64 = %e tick\n" , $timetick64 ;

}

sub do_Mem_avail_Info{
    my $rt = shift;
    my $fho = shift;

    return unless $rt->i('new_AEEFreeRAM');
    print {$fho} "-"x145,$/;
    print {$fho} "Memery available Info$/";
    print {$fho} "-"x145,$/;
    my $MFW_MbCrtl = $rt->g('gCCI_MFW_MbCrtl');
    my $MM_SYS_MbCrtl = $rt->g('gCCIMM_SYS_MbCrtl');
    my $GPF_MbCrtl = $rt->g('gCCI_GPF_MbCrtl');
    my $new_AEEFreeRAM = $rt->g('new_AEEFreeRAM');
 
    my ($CCI_MFW_mbSize,$TP1,$TP2,$CCI_MFW_used) = unpack "LLLL", substr($MFW_MbCrtl, 0, 4*4);
    my ($CCI_MFW_AVAIL) =$CCI_MFW_mbSize -$CCI_MFW_used ;
    
    my ($MM_SYS_mbSize,$TP3,$TP4,$MM_SYS_used) = unpack "LLLL", substr($MM_SYS_MbCrtl, 0, 4*4);
    my ($MM_SYS_AVAIL) =$MM_SYS_mbSize -$MM_SYS_used ;

    my ($GPF_mbSize,$TP5,$TP6,$GPF_used) = unpack "LLLL", substr($GPF_MbCrtl, 0, 4*4);
    my ($GPF_AVAIL) =$GPF_mbSize -$GPF_used ;

    my ($gnew_AEEFreeRAM) = unpack "L", substr($new_AEEFreeRAM, 0, 4);

    printf "CCI_MFW_avail = %d Byte = %d KB\n" , $CCI_MFW_AVAIL , $CCI_MFW_AVAIL/1024 ;
    printf "CCI_MM_SYS_avail =%d Byte = %d KB\n" , $MM_SYS_AVAIL , $MM_SYS_AVAIL/1024 ;
    printf "CCI_GPF_avail = %d Byte = %d KB\n" ,$GPF_AVAIL , $GPF_AVAIL/1024 ;
    printf "new_AEEFreeRAM = %d Byte = %d KB\n" , $gnew_AEEFreeRAM , $gnew_AEEFreeRAM/1024;
  
}

sub do_g_Gpf2RexQueuePtrTable {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('Gpf2RexQueuePtrTable');
    print {$fho} "-" x 20, "contents of Gpf2RexQueuePtrTable", "-" x 20, "$/";
    my $size                   = $rt->i('Gpf2RexQueuePtrTable')->{Size};
    my $Gpf2RexQueuePtrTable   = $rt->g('Gpf2RexQueuePtrTable');
    my $Gpf2RexTaskTcbPtrTable = $rt->g('Gpf2RexTaskTcbPtrTable');
    my $p                      = 0;
    my $index                  = 0;
    while ( $p < $size ) {
        my ($pGpfQueuePtr) = unpack "L", substr( $Gpf2RexQueuePtrTable, $p, 4 );
        my ($pGpfTcbPtr) = unpack "L", substr( $Gpf2RexTaskTcbPtrTable, $p, 4 );
        my $fnp = $pGpfTcbPtr + 144;
        my $filename = unpack "Z*", $rt->rget( $fnp, 100 );
        if ( $pGpfQueuePtr > 0 ) {
            printf {$fho} "Gpf2RexQueuePtrTable[%2d] :: 0x%08x tcb:0x%08x %s$/",
              $index, $pGpfQueuePtr, $pGpfTcbPtr, $filename;
        }
        $p     += 4;
        $index += 1;
    }
}

sub do_g_Gpf2RexQueueLinkTable {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('Gpf2RexQueueLinkTable');
    print {$fho} "-" x 20, "contents of Gpf2RexQueueLinkTable", "-" x 20, "$/";
    my $size                  = $rt->i('Gpf2RexQueueLinkTable')->{Size};
    my $Gpf2RexQueueLinkTable = $rt->g('Gpf2RexQueueLinkTable');
    my $p                     = 0;
    my $index                 = 0;
    while ( $p < $size ) {
        my ( $next_ptr, $prev_ptr, $cnt ) = unpack "LLL",
          substr( $Gpf2RexQueueLinkTable, $p, 4 * 3 );
        if ( $next_ptr > 0 ) {
            printf {$fho}
"Gpf2RexQueueLinkTable[%2d] :: nextPtr:0x%08x prevPtr:0x%08x cnt:%d $/",
              $index, $next_ptr, $prev_ptr, $cnt;
        }
        $p += 4 * 3;
        $index += 1;
    }

}

sub do_g_Gpf2RexQueueDataTable {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('Gpf2RexQueueDataTable');
    print {$fho} "-" x 20, "contents of Gpf2RexQueueDataTable", "-" x 20, "$/";
    my $size                   = $rt->i('Gpf2RexQueueDataTable')->{Size};
    my $Gpf2RexQueueDataTable  = $rt->g('Gpf2RexQueueDataTable');
    my $Gpf2RexTaskTcbPtrTable = $rt->g('Gpf2RexTaskTcbPtrTable');
    my $p                      = 0;
    my $p1                     = 0;
    my $idxRow                 = 0;
    my $idxCol                 = 0;
    my $showTaskName           = 1;

    print {$fho} "nextPtr    prevPtr    type       opc        usrData $/";
    print {$fho} "-" x 100, "$/";

    while ( $p < $size ) {
        my ( $next_ptr, $prev_ptr, $type, $opc, $usrData ) = unpack "LLLLL",
          substr( $Gpf2RexQueueDataTable, $p, 4 * 5 );
        if ( $next_ptr > 0 ) {
            if ( $showTaskName == 1 ) {
                my ($pGpfTcbPtr) = unpack "L", substr($Gpf2RexTaskTcbPtrTable, $p1, 4);
                my $fnp = $pGpfTcbPtr + 144;
                my $TaskName = unpack "Z*", $rt->rget($fnp, 100);
                printf {$fho} "%s$/", $TaskName;
                $showTaskName = 0;
            }
            printf {$fho} "0x%08x 0x%08x ", $next_ptr, $prev_ptr;
            printf {$fho} "0x%08x 0x%08x 0x%08x$/", $type, $opc, $usrData;
        }
        $p += 4 * 5;
        $idxCol += 1;
        if ( $idxCol == 200 ) {
            $p1     += 4;
            $idxRow += 1;
            $idxCol = 0;
            $showTaskName = 1;
        }
    }
}

sub do_g_SpOverflowDetect{
    my $rt = shift;
    my $fho = shift;
    return unless $rt->i('dog_SpOverFlow_Detect');
		my @SpOverFlowDetect = (
		"dog_SpOverFlow_Detect",
		"mdsp_SpOverFlow_Detect",
		"qdsp_SpOverFlow_Detect",
		"voc_SpOverFlow_Detect",
		"snd_SpOverFlow_Detect",
		"nv_SpOverFlow_Detect",
		"fs_SpOverFlow_Detect",
		"hs_SpOverFlow_Detect",
		"diag_SpOverFlow_Detect",
		"qdiag_SpOverFlow_Detect",
		"cm_SpOverFlow_Detect",
		"bt_SpOverFlow_Detect",
		"bt_pf_SpOverFlow_Detect",
		"bt_fs_SpOverFlow_Detect",
		"ui_SpOverFlow_Detect",
		"wms_SpOverFlow_Detect",
		"timer_SpOverFlow_Detect",
		"sleep_SpOverFlow_Detect",
		"ecall_app_SpOverFlow_Detect",
		"ecall_ivs_SpOverFlow_Detect",
		"ds_SpOverFlow_Detect",
		"dswcsd_ul_SpOverFlow_Detect",
		"dswcsd_dl_SpOverFlow_Detect",
		"Gcsd_SpOverFlow_Detect",
		"secssl_SpOverFlow_Detect",
		"uim_SpOverFlow_Detect",
		"vs_SpOverFlow_Detect",
		"graph_SpOverFlow_Detect",
		"camera_drv_SpOverFlow_Detect",
		"mmoc_SpOverFlow_Detect",
		"tmc_SpOverFlow_Detect",
		"gsdi_SpOverFlow_Detect",
		"gstk_SpOverFlow_Detect",
		"wcdma_mac_hs_dl_SpOverFlow_Detect",
		"rrc_SpOverFlow_Detect",
		"gsm_l1_SpOverFlow_Detect",
		"gsm_l2_SpOverFlow_Detect",
		"rr_SpOverFlow_Detect",
		"gprs_mac_SpOverFlow_Detect",
		"gprs_rlc_ul_SpOverFlow_Detect",
		"gprs_rlc_dl_SpOverFlow_Detect",
		"gprs_llc_SpOverFlow_Detect",
		"tc_SpOverFlow_Detect",
		"mm_SpOverFlow_Detect",
		"cb_SpOverFlow_Detect",
		"sm_SpOverFlow_Detect",
		"reg_SpOverFlow_Detect",
		"mn_cnm_SpOverFlow_Detect",
		"mgpmc_SpOverFlow_Detect",
		"pp_SpOverFlow_Detect",
		"cc_SpOverFlow_Detect",
		"pgi_SpOverFlow_Detect",
		"gpsfft_SpOverFlow_Detect",
		"cd_SpOverFlow_Detect",
		"nf_SpOverFlow_Detect",
		"lm_SpOverFlow_Detect",
		"sm_tm_SpOverFlow_Detect",
		"pdcommtcp_SpOverFlow_Detect",
		"pdcommwms_SpOverFlow_Detect",
		"ftm_SpOverFlow_Detect",
		"qvp_ae_task_SpOverFlow_Detect",
		"qvp_mpeg4_SpOverFlow_Detect",
		"qvp_app_SpOverFlow_Detect",
		"qvpio_SpOverFlow_Detect",
		"qvppl_SpOverFlow_Detect",
		"qvp_vfe_SpOverFlow_Detect",
		"ims_media_SpOverFlow_Detect",
		"ims_SpOverFlow_Detect",
		"ims_cb_SpOverFlow_Detect",
		"pbm_SpOverFlow_Detect",
		"ats_SpOverFlow_Detect",
		"disp_SpOverFlow_Detect",
		"cnv_SpOverFlow_Detect", 
		"dmtask_SpOverFlow_Detect",
		"fc_SpOverFlow_Detect",
		"qtv_video_renderer_SpOverFlow_Detect",
		"qtv_audio_SpOverFlow_Detect",
		"qtv_task10_SpOverFlow_Detect",
		"tcxomgr_SpOverFlow_Detect",
		"qtv_dec_dlAgenttask_SpOverFlow_Detect",
		"videoshare_SpOverFlow_Detect",  
		"qtv_dec_dlDspSvctask_SpOverFlow_Detect",
		"chg_SpOverFlow_Detect",
		"akt_SpOverFlow_Detect",
		"datasync_SpOverFlow_Detect",
		"vrntts_SpOverFlow_Detect",
		"wap_SpOverFlow_Detect",
		"filemgr_SpOverFlow_Detect",
		"phbk_SpOverFlow_Detect",
		"msg_SpOverFlow_Detect",
		"java_SpOverFlow_Detect",
		"kve_SpOverFlow_Detect",
		"http_SpOverFlow_Detect",
		"mcdc_SpOverFlow_Detect",
		"sys_task_SpOverFlow_Detect",
		"fmr_SpOverFlow_Detect",
		"ccimm_SpOverFlow_Detect",
		"misc_SpOverFlow_Detect",
		"ccimtp_SpOverFlow_Detect");

    print {$fho} "-"x20, "contents of SpOverFlowDetect", "-"x20, "$/";		

		foreach my $currName (@SpOverFlowDetect) {
			my $currAddr = $rt->g($currName);
      my ($currValue) = unpack "L", substr($currAddr, 0, 4);			
			if ($currValue != 0x16836505){
				printf {$fho} "$currName" . "::0x%08x" . "   <-----OverFlow$/", $currValue;
			}
			else{
				printf {$fho} "$currName" . "::0x%08x$/", $currValue;
			}
		}
}

sub do_version_info {
    my $rih  = shift;
    my $eih  = shift;
    my $hint = shift;

    print "-" x 146, $/;
    print pack "A13A1A8A1A55A1A55A1A1", qw(name | addr | ramdump | elf | diff);
    print $/;
    print "-" x 146, $/;
    foreach ( @{$hint} ) {
        my ( $name, $addr ) = @{$_};
        $rih->{$name} =~ s/\n/\\n/g;
        $eih->{$name} =~ s/\n/\\n/g;
        print pack "A13A1A8A1A55A1A55A1A1", $name, "|",
          sprintf( "%08x", $addr ), "|", $rih->{$name}, "|", $eih->{$name}, "|",
          ( $rih->{$name} eq $eih->{$name} ) ? "" : "x";
        print $/;
    }
}

sub do_stamp {
    my $rd_fn  = shift;
    my $elf_fn = shift;
    my $fho    = *STDOUT;
    my $rt     = Runtime->new( $rd_fn, $elf_fn );
    my $hint   = get_info_pos();
    my $rih    = rd_get_info( $rt, $hint );
    my $eih    = elf_get_info( $rt, $hint );
    do_version_info( $rih, $eih, $hint );
}

sub do_version {
    my $rd_fn = shift;
    my $fho   = *STDOUT;
    my $rt    = Runtime->new($rd_fn);
    my $hint  = get_info_pos();
    my $rih   = rd_get_info( $rt, $hint );
    print {$fho} $rih->{ver_sw}, $/;
}

sub do_GPF_GetMaxFreeBlkSizeInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    my $gCCI_GPF_MbCrtl = $rt->g('gCCI_GPF_MbCrtl');
    my $MaxSize = 0;
    my $i = 0;
    my $p = 4 + 4 + 4 + 4 + 4 + 4 + 16;

    for ($i = 0; $i < 16; $i++)
    {
        my ( $pHeader ) = unpack "L",
              substr( $gCCI_GPF_MbCrtl, $p, 4 );
        my $currentItem = $pHeader;
        while( $currentItem != 0x00000000 && $currentItem != 0xFFFFFFFF )
        {
            my $buffer = $rt->rget($currentItem, 4*7);
            my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
            = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );


            if ( $nSize > $MaxSize && $poolNext != 0x00000000 )
            {
                $MaxSize = $nSize;
            }

            $currentItem = $poolNext;
        }
        $p += 4;
    }

    printf {$fho} "GPF_MaxFreeBlkSize--$MaxSize$/";
}

sub do_MFW_GetMaxFreeBlkSizeInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    my $gCCI_MFW_MbCrtl = $rt->g('gCCI_MFW_MbCrtl');
    my $MaxSize = 0;
    my $i = 0;
    my $p = 4 + 4 + 4 + 4 + 4 + 4 + 16;

    for ($i = 0; $i < 16; $i++)
    {
        my ( $pHeader ) = unpack "L",
              substr( $gCCI_MFW_MbCrtl, $p, 4 );
        my $currentItem = $pHeader;
        while( $currentItem != 0x00000000 && $currentItem != 0xFFFFFFFF )
        {
            my $buffer = $rt->rget($currentItem, 4*7);
            my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
            = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );


            if ( $nSize > $MaxSize && $poolNext != 0x00000000 )
            {
                $MaxSize = $nSize;
            }

            $currentItem = $poolNext;
        }
        $p += 4;
    }

    printf {$fho} "MFW_MaxFreeBlkSize--$MaxSize$/";
}

sub do_SYS_GetMaxFreeBlkSizeInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OpenMemMonitor');
    my $gCCIMM_SYS_MbCrtl = $rt->g('gCCIMM_SYS_MbCrtl');
    my $MaxSize = 0;
    my $i = 0;
    my $p = 4 + 4 + 4 + 4 + 4 + 4 + 16;

    for ($i = 0; $i < 16; $i++)
    {
        my ( $pHeader ) = unpack "L",
              substr( $gCCIMM_SYS_MbCrtl, $p, 4 );
        my $currentItem = $pHeader;
        while( $currentItem != 0x00000000 && $currentItem != 0xFFFFFFFF )
        {
            my $buffer = $rt->rget($currentItem, 4*7);
            my ( $prevItem, $nextItem, $poolNext, $nSize, $filename, $nline, $lr ) 
            = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );


            if ( $nSize > $MaxSize && $poolNext != 0x00000000 )
            {
                $MaxSize = $nSize;
            }

            $currentItem = $poolNext;
        }
        $p += 4;
    }

    printf {$fho} "SYS_MaxFreeBlkSize--$MaxSize$/";
}

sub do_ShowHeapMaxSizeInfo {
    my $rt  = shift;
    my $fho = shift;
    my @MbCtrl = qw(gCCIMM_SYS_MbCrtl gCCI_MFW_MbCrtl gCCI_GPF_MbCrtl);
    print {$fho} "-" x 80, "$/";
    print {$fho} "ShowHeapMaxSizeInfo$/";
    print {$fho} "-" x 80, "$/";
    my $gk1KHeapSize = $rt->i('gk1KHeapArr')->{Size};
    printf {$fho} "k1kheap::"."%d btyes$/", $gk1KHeapSize;
    foreach my $i (@MbCtrl) {
        my $currMbCtrl = $rt->g("$i");        
        my ( $size, $pHeader, $pFreeHeader, $used ) 
        = unpack "LLLL", substr( $currMbCtrl, 0, 4*4 );
        printf {$fho} "$i"."::%d btyes$/", $size;
    }
}

sub do_ShowIpcMemInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('ipcmem_pool_info');
    print {$fho} "-" x 80, "$/";
    print {$fho} "do_ShowIpcMemInfo$/";
    print {$fho} "-" x 80, "$/";
#    printf {$fho} pack "x2A8x5A6x7A4x7A4", "PoolSize", "MaxNum", "Mask", "Used";
    printf {$fho} "  PoolSize     MaxNum       Mask       Used$/";
    my $i = 0;
    my $variableName = "ipcmem_pool_info";
    
    do {
        printf {$fho} "$/";
        my $size = $rt->i($variableName)->{Size};
        my $ipcmem_pool_info = $rt->g($variableName);

        my $p = 0;
        while ( $p < $size ) {
            my ( $poolsize, $totalnum,  $mask, $used ) = unpack "SSSS",
              substr( $ipcmem_pool_info, $p, 2 * 4 );
            $p += 2 * 4;

            printf {$fho} "%10d %10d %10d %10d$/"
                , $poolsize, $totalnum, $mask, $used;
        }
        $variableName = $variableName . "_SameNameItem$i";
        $i++;
    }while ( $rt->i($variableName) );
}

sub do_DumpJavaTraceBuff {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('l_javaTraceBuffer');
    print {$fho} "-" x 80, "$/";
    print {$fho} "do_DumpJavaTraceBuff$/";
    print {$fho} "-" x 80, "$/";
    my $size = $rt->i('l_javaTraceBuffer')->{Size};
    my $l_javaTraceBuffer = $rt->g('l_javaTraceBuffer');

    print {$fho} unpack "Z*", $l_javaTraceBuffer;
}

sub do_parsePageFaultIP {
    my $rt    = shift;
    my $fho   = shift;

    my $consoleout = rd_get_console($rt);
    print {$fho} "-" x 70, $/, "Unhandled page fault Function\n" . "-" x 70, $/;
    my $pageFaultIdx = index( $consoleout, "Unhandled page fault:" );

    while ( $pageFaultIdx > 0 )
    {
        my $ipStartIdx = index( $consoleout, "ip=", $pageFaultIdx ) + 3;
        return unless ( $ipStartIdx > 3 );
        my $ipEndIdx = index( $consoleout, ",", $ipStartIdx );
        my $ipAddr = hex( substr( $consoleout, $ipStartIdx, $ipEndIdx-$ipStartIdx ) );
        my $ipsym = $rt->locate_symbol($ipAddr);
        printf {$fho} "0x%08x\t\t%s()$/", $ipAddr, $ipsym;
        $pageFaultIdx = index( $consoleout, "Unhandled page fault:", $ipEndIdx );
    }
}

sub do_ArcCallerInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('ArcCallerInfo');
    print {$fho} "-" x 40, "contents of ArcCallerInfo$/";
    my $size        = $rt->i('ArcCallerInfo')->{Size};
    my $ArcCallerInfo = $rt->g('ArcCallerInfo');
    my $p           = 0;
    while ( $p < $size ) {
        my ( $lrp, $nAddr, $nAllocSize ) = unpack "LLL",
          substr( $ArcCallerInfo, $p, 4 * 3 );
        my $lrpsym = $rt->locate_symbol($lrp);
        $p += 4 * 3;
        next unless $nAllocSize > 0;
        printf {$fho} "0x%08x %010d 0x%08x %s$/", $nAddr, $nAllocSize, $lrp,
          $lrpsym;
    }
}

sub do_MCCallerInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('MCCallerInfo');
    print {$fho} "-" x 40, "contents of MCCallerInfo$/";
    my $size        = $rt->i('MCCallerInfo')->{Size};
    my $MCCallerInfo = $rt->g('MCCallerInfo');
    my $p           = 0;
    while ( $p < $size ) {
        my ( $lrp, $nAddr, $nAllocSize ) = unpack "LLL",
          substr( $MCCallerInfo, $p, 4 * 3 );
        my $lrpsym = $rt->locate_symbol($lrp);
        $p += 4 * 3;
        next unless $nAllocSize > 0;
        printf {$fho} "0x%08x %010d 0x%08x %s$/", $nAddr, $nAllocSize, $lrp,
          $lrpsym;
    }
}

sub read_hashfile {
    my $hashfile = shift;
    my %qhash;
    open my $fhh, '<', $hashfile or die "Can't open hashfile $hashfile.$!\n";

    while(<$fhh>) {
	if(/^(\d*):([\w\.]+):(.*)/) {
	    $qhash{$1} = [$2,$3];
	} else {
	    # print "Ignoring hash line: $_\n";
	}
    }
    close $fhh;
    return \%qhash;
}

sub do_ShowHandsetInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('dm_imeibcd');
    print {$fho} "-" x 2, "contents of do_ShowHandsetInfo$/";
    my $size = $rt->i('dm_imeibcd')->{Size};
    my $imei = $rt->g('dm_imeibcd');
    my $p = 0;

    print {$fho} "IMEI:";
    while ( $p < $size ) {
        my $CurrData = unpack "C",
          substr( $imei, $p, 1 );
        $p++;
        printf {$fho} "0x%02x ", $CurrData;
    }
    print {$fho} $/;

    if ( $rt->i('l_imsi_SameNameItem0') ) {
        my $imsi = $rt->g('l_imsi_SameNameItem0');
        $size = $rt->i('l_imsi_SameNameItem0')->{Size};
        $p = 0;
        print {$fho} "IMSI:";
        while ( $p < $size ) {
            my $CurrData = unpack "C",
              substr( $imsi, $p, 1 );
            $p++;
            printf {$fho} "0x%02x ", $CurrData;
        }
        print {$fho} $/;
    }

    my $hw_ver = $rt->g('ver_hw');
    print {$fho} "HW Version:";
    print {$fho} unpack "Z*", $hw_ver;
    print {$fho} $/;

    return unless $rt->i('g_mfwa_nm_qcvar');
    my $g_mfwa_nm_qcvar = $rt->g('g_mfwa_nm_qcvar');
    my $mnc = unpack "L", substr( $g_mfwa_nm_qcvar, 20, 4 );
    printf {$fho} "MNC:%d$/", $mnc;
    my $mcc = unpack "L", substr( $g_mfwa_nm_qcvar, 24, 4 );
    printf {$fho} "MCC:%d$/", $mcc;    
}

=comment
typedef struct
{
	cChar *fileName;
	cS32 fd;
	E_FILEMGR_STORAGE storage;
	cU8 isAppend;
	cU8 isFast;
	cU8 isUsed;
	cU8 openType;
	E_FILEMGR_OPEN_MODE openMode;
	cU8 isSeek;
	cU8 whence;
	cU32 offset;
	cU8 isDRM;
	cU32 secHandleID;
	cU32 returnAddr;
	T_FILEMGR_ENTRY_INFO entryInfo;
} T_FILEMGR_FILE_HANDLE;
=cut

sub do_parseFileHandleInfo {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('gFileHandle');
    print {$fho} "-" x 40, "contents of FileHandleInfo$/";
    my $OldVersionSize = 12400;
    my $size = $rt->i('gFileHandle')->{Size};
    my $gFileHandle = $rt->g('gFileHandle');
    my $maxFileHandleNum = 100;
    if ( $size == $OldVersionSize ) {
        $maxFileHandleNum = 100;
    }
    elsif ( $size > $OldVersionSize ) {
        print {$fho} "Different Structure Size$/";
    }
    else {
        $maxFileHandleNum = 50;
    }
    
    my $pOffset = $size / $maxFileHandleNum;
    my $p = 0;
    while ( $p < $size ) {
        my $fileName = unpack "L", substr( $gFileHandle, $p, 4 );
        my $fd = unpack "L", substr( $gFileHandle, ($p + 4), 4 );
        my $isUsed = unpack "C", substr( $gFileHandle, ($p + 11), 1 );
        my $openMode = unpack "C", substr( $gFileHandle, ($p + 13), 1 );
        my $returnAddr = unpack "L", substr( $gFileHandle, ($p + 28), 4 );

        if ( $isUsed == 1 ) {
            my $fileNameStr = " ";
            if ( $fileName != 0x00000000 ) {
                $fileNameStr = unpack "Z*", $rt->rget( $fileName, 100 );
            }
            my $lrpsym = $rt->locate_symbol($returnAddr);
            my $type = $rt->i($lrpsym)->{Type};
            if ( $rt->i($lrpsym)->{Type} eq 'OBJECT' ) {
                $lrpsym = "";
            }

            if  ( $maxFileHandleNum == 50 ) {
                my $tickCount = unpack "L", substr( $gFileHandle, ($p + 32), 4 );
                printf {$fho} "tick:%10u\t", $tickCount;
            }

            printf {$fho} "fd:$fd\t\topenMode:$openMode\tLR:0x%08x\t".pack( "A30", $lrpsym )."\tFileName:0x%08x\t$fileNameStr"
                , $returnAddr, $fileName;

            print {$fho} $/;
        }
        $p += $pOffset;
    }
}

sub do_current_call_stack {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('rex_core');
    my $rex_core = $rt->g('rex_core');
    my $regs_off = 12;

    my (
    $r0, $r1,  $r2,  $r3,  $r4, $r5, $r6, $r7, $r8,
    $r9, $r10, $r11, $r12, $r13_svc, $r14_svc, $spsr_svc,
    $pc, $r13_usr, $r14_usr
    ) = unpack( "L19", substr( $rex_core, $regs_off, 4 * 19 ) );

    print {$fho} "-" x 70, $/;
    print {$fho} "Rex Core Registers$/";
    print {$fho} "-" x 70, $/;

    print {$fho} pack "A9A9A9A9A9A9A9A9A9A9A9A9A9A9A9A9",
      qw(sp lr pc r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12);
    print {$fho} $/;
    print {$fho} "-" x 145, $/;
    printf {$fho}
    "%08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x %08x",
    $r13_usr, $r14_usr, $pc, $r0, $r1, $r2, $r3, $r4, $r5, $r6, $r7, $r8, $r9, $r10, $r11, $r12;
    print {$fho} $/;

    return unless $rt->i('err_fatal_dump');
    my $err_fatal_dump = $rt->g('err_fatal_dump');
    my $stackframe_off = 24;
    my $currsp = $r13_usr;
    my $i = 0;

    my $taskname = unpack "Z*", substr( $err_fatal_dump, 8, 15 );
    print {$fho} "-" x 70, $/;
    print {$fho} "Running Call stack of task ", $taskname, $/;
    print {$fho} "-" x 70, $/;
    for ($i = 0; $i < 256; $i++) {
        my $value = unpack "L", substr( $err_fatal_dump, $stackframe_off, 4 );
        if ( $value > 0x1000 ) {
            my $symbol = $rt->locate_symbol($value);
            my $off = $value - $rt->i($symbol)->{Value};
            my $str = "";
            if ( $rt->i($symbol)->{Type} eq 'OBJECT' ) {
            }
            elsif ( $rt->i($symbol)->{Type} eq 'FUNC' ) {
                printf {$fho} "0x%08x 0x%08x %8d %8d %s\n",
                  $currsp, $value, $off, $rt->i($symbol)->{Size},
                  pack( "A7A21A40", $rt->i($symbol)->{Type}, $str, $symbol );
            }
        }
        else {
            #			printf "0x%08x 0x%08x %8d\n", $p+$sp, $value, $value;
        }
        $stackframe_off += 4;
        $currsp += 4;
    }
}

sub do_at_time_history {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('cci_at_time_history');
    my $cci_at_time_history = $rt->g('cci_at_time_history');
    my $totalSize = $rt->i('cci_at_time_history')->{Size};
    my $maxItemNum = 21;
    my $everyItemSize = $totalSize / $maxItemNum;
    my $i = 0;
    my $offset = 0;

    print {$fho} "-" x 70, $/;
    print {$fho} "at_time_history$/";
    print {$fho} "-" x 70, $/;    
    
    for ($i = 0; $i < $maxItemNum; $i++) {
        my $strLen = 560;
        my $buffStr = unpack "Z*", substr( $cci_at_time_history, $offset, $strLen );
        my ($response, $time) = unpack "LL", substr( $cci_at_time_history, $offset+$strLen, 4 * 2 ); 
        $offset += $everyItemSize;
        if ( $response != 0 || $time != 0 ) {
            print {$fho} $buffStr, $/;
            print {$fho} "Response:$response  time:$time$/";
        }
    }
}

sub do_CCI_PartitionPoolInfo{
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('OEMHeapPoolInfo');
    print {$fho} "-" x 145, $/;
    print {$fho} "CCI Partition Pool info$/";
    print {$fho} "-" x 145, $/;
    my $OEMHeapPoolInfo = $rt->g('OEMHeapPoolInfo');
    my $size = $rt->i('OEMHeapPoolInfo')->{Size};
    my $p = 0;
    while ($p < 10)
    {
        my ( $pPoolHeader ) = unpack "L",
              substr( $OEMHeapPoolInfo, ($p*4) , 4 );
        my $currentPool = $pPoolHeader;
        
        printf {$fho} "OEMHeapPoolInfo.pHeapPool[%d]:", $p;
        if ($currentPool != 0x00000000)
        {
            printf {$fho} $/;
        }
        else
        {
            printf {$fho} "No Pool$/";
        }
        while ( $currentPool != 0x00000000 ) 
        {
            my $buffer = $rt->rget($currentPool, 4*7);
            my ( $prevPool, $nextPool, $nFreeSize, $nUsedSize, $nPoolNo, $pFreeNodePtr, $pNodePtr ) 
            = unpack "LLLLLLL", substr( $buffer, 0, 4*7 );

            printf {$fho} "0x%08x$/", $currentPool;
            printf {$fho} "FreeSize = %d$/", $nFreeSize;
            printf {$fho} "Used = %d$/", $nUsedSize;
            printf {$fho} $/;

            $currentPool = $nextPool;
            if ( $currentPool == $pPoolHeader )
            {
                $currentPool = 0x00000000;
            }
        }
        $p += 1;
    }
    my ( $Pool0, $Pool1, $Pool2, $Pool3, $Pool4, $Pool5, $Pool6, $Pool7, $Pool8, $Pool9 ) = unpack "LLLLLLLLLL",
          substr( $OEMHeapPoolInfo, ($p*4) , 4*10 );
          
    printf {$fho} "OEMHeapPoolInfo.Used = ( %d, %d, %d, %d, %d, %d, %d, %d, %d, %d)$/",
          $Pool0, $Pool1, $Pool2, $Pool3, $Pool4, $Pool5, $Pool6, $Pool7, $Pool8, $Pool9;

    $p += 10;
    ( $Pool0, $Pool1, $Pool2, $Pool3, $Pool4, $Pool5, $Pool6, $Pool7, $Pool8, $Pool9 ) = unpack "LLLLLLLLLL",
          substr( $OEMHeapPoolInfo, ($p*4) , 4*10 );

    printf {$fho} "OEMHeapPoolInfo.Count = ( %d, %d, %d, %d, %d, %d, %d, %d, %d, %d)$/",
          $Pool0, $Pool1, $Pool2, $Pool3, $Pool4, $Pool5, $Pool6, $Pool7, $Pool8, $Pool9;

}

sub parse_k1Heap {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('gk1KHeapArr');
    my $gk1KHeapArr = $rt->g('gk1KHeapArr');
    my $HNODE_FLAG_FREE_MASK = 0x0100;
    my $HNODE_FLAG_BUSY_MASK = 0x0200;
    my $HNODE_FLAG_AUXHDR_MASK = 0x04000000;
    my $HNODE_FLAG_LEFT_MASK = 0x01000000;
    my $HNODE_FLAG_RIGHT_MASK = 0x02000000;
    my $HNODE_FLAG_DELAY_MASK = 0x04000;

    my $HNODE_FLAG_RIGHT=1;
    my $freeBytesCount=0;
    my $busyBytesCount=0;
    my $freeNodesCount=0;
    my $busyNodesCount=0;
    my $maxFreeNodeSize=0;
    my $maxBusyNodeSize=0;

    my $piHeap1 = unpack "L", substr( $gk1KHeapArr, 0, 4 );
    if ( $piHeap1 == 0 ) {return;}
    my $IHeap1DebugCtlSize = 1836; #sizeof(IHeap1DebugCtl)
    my $IHeap1DebugCtl = $rt->rget( $piHeap1, $IHeap1DebugCtlSize );

    my $dwTotalBytes = unpack "L", substr( $IHeap1DebugCtl, 1820, 4 ); #piHeap1->dwTotalBytes
    my $dwFreeBytes = unpack "L", substr( $IHeap1DebugCtl, 1828, 4 ); #piHeap1->dwFreeBytes
    my $pHeapNode= unpack "L", substr( $IHeap1DebugCtl, 1784, 4 ); #piHeap1->pFirstNode

    print {$fho} "-" x 145, $/;
    print {$fho} "Parse k1Heap!!!$/";
    print {$fho} pack "A11A11A11A11A9A11A11",
          qw(address pLink1 pLink2 pLink3 dwSize dwFlags NodeTrailder);
    print {$fho} $/;
    print {$fho} "-" x 145, $/;

    while ( $HNODE_FLAG_RIGHT != 0 ) {
        my $owner="";
        my $debugStringAtom="";
        my $validpLink2=1;
        my $Hnode_Size = 20; #sizeof(_HNode);
        my ($pLink1, $pLink2, $pLink3, $dwSize, $dwFlags) = unpack "LLLLL", $rt->rget( $pHeapNode, $Hnode_Size );

        $HNODE_FLAG_RIGHT=$dwFlags&($HNODE_FLAG_RIGHT_MASK);            
        last if $HNODE_FLAG_RIGHT == 0;
        my $pNodeTrailer = $pHeapNode + $Hnode_Size + $dwSize;
        my $HnodeTrailer_Size = 4; #sizeof(struct _HNodeTrailer)
        my $NodeTrailder = unpack "L", $rt->rget( $pNodeTrailer, $HnodeTrailer_Size );

        my $HNODE_FLAG_FREE=$dwFlags&($HNODE_FLAG_FREE_MASK);
        my $HNODE_FLAG_BUSY=$dwFlags&($HNODE_FLAG_BUSY_MASK);
        my $HNODE_FLAG_AUXHDR=$dwFlags&($HNODE_FLAG_AUXHDR_MASK);
        my $HNODE_FLAG_LEFT=$dwFlags&($HNODE_FLAG_LEFT_MASK);
        my $HNODE_FLAG_DELAY=$dwFlags&($HNODE_FLAG_DELAY_MASK);
        my $free = 3; #Unknow

        if ( $HNODE_FLAG_BUSY != 0 ) {
            $busyBytesCount = $busyBytesCount + $dwSize;
            $busyNodesCount= $busyNodesCount + 1;

            if ( $dwSize > $maxBusyNodeSize ) {
                $maxBusyNodeSize = $dwSize;
            }
            $free = 0;
        }
        elsif ( $HNODE_FLAG_FREE != 0 ) {
            $freeBytesCount = $freeBytesCount + $dwSize;
            $freeNodesCount = $freeNodesCount + 1;

            if ( $dwSize > $maxFreeNodeSize ){
                $maxFreeNodeSize = $dwSize;
            }

            $free = 1;
        }
        elsif ( $HNODE_FLAG_DELAY != 0 ) {
            $free = 2;
        }
        else {
        }

        if ( $pHeapNode != $NodeTrailder ) {
            printf {$fho} "0x%08x 0x%08x 0x%08x 0x%08x %8d 0x%08x 0x%08x", 
                $pHeapNode, $pLink1, $pLink2, $pLink3, $dwSize, $dwFlags, $NodeTrailder; 

            print {$fho} " free: $free";
            print {$fho} " ERROR!!! NodeTrailer is corrupted!! ";
            print {$fho} $/;
        }

        $pHeapNode =  $pHeapNode + $Hnode_Size + $dwSize + $HnodeTrailer_Size;        
    }

    print {$fho} "FreeBtyesCount = $freeBytesCount$/";
    print {$fho} "BusyBtyesCount = $busyBytesCount$/";
    print {$fho} "FreeNodesCount = $freeNodesCount$/";
    print {$fho} "BusyNodesCount = $busyNodesCount$/";
    print {$fho} "maxFreeNodeSize = $maxFreeNodeSize$/";
    print {$fho} "maxBusyNodeSize = $maxBusyNodeSize$/";
}

=comment
typedef struct{
    int TopAPID;
    int TopModID;
    MfwEvt KeyEvent;
    U8 KeyCode;
}ApControlKeyEventLogType;
=cut

sub parseKeyLog {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('keylog');
    print {$fho} "-" x 145, $/;
    print {$fho} "Parser KeyLog!!!$/";
    print {$fho} "-" x 145, $/;
    my $pCurrkeylog = unpack "L", $rt->g('pCurrkeylog');
    my $keylogAddr = $rt->i('keylog')->{Value};
    my $keylogArr = $rt->g('keylog');
    my $totalSize = $rt->i('keylog')->{Size};
    my $keyItemSize = 16; #sizeof(ApControlKeyEventLogType)
    my $p = 0;

    while( $p < $totalSize ) {
        my ( $TopAPID, $TopModeID, $keyEvent, $KeyCode ) = unpack "LLLL", 
            substr( $keylogArr, $p, $keyItemSize );
        printf {$fho} "TopAPID:%02d TopModeID:%03d keyEvent:0x%08x KeyCode:%02d ",
            $TopAPID, $TopModeID, $keyEvent, $KeyCode;

        if ( $keylogAddr == $pCurrkeylog ) {
            print {$fho} "<--CurrKeyLog";
        }
        print {$fho} $/;
        $p += $keyItemSize;
        $keylogAddr += $keyItemSize;
    }
}

sub checkDelayListData {
    my $rt  = shift;
    my $fho = shift;

    return unless $rt->i('gk1KHeapArr');
    my $pHeapCtrl = unpack "L", substr( $rt->g('gk1KHeapArr'), 0, 4 );
    my $pDelayList = $pHeapCtrl + 1816;
    my @NodeList;

    my $pDelayListNodeAddr = unpack"L", $rt->rget( $pDelayList, 4 );
    if ( $pDelayListNodeAddr != 0 ) {
        print {$fho} "-" x 145, $/;
        print {$fho} "checkDelayListData!!!$/";
        print {$fho} "-" x 145, $/;
        my ( $ppWalk, $ppEnd, $aDelay ) = unpack "LLL", $rt->rget( $pDelayListNodeAddr, 4 * 3 );
        my $pDelayArr = $pDelayListNodeAddr + 8;
        my $offset = 4;
        my $pTempNode = $aDelay;

        while ( $pTempNode != 0 ) {
#            printf {$fho} "0x%08x 0x%08x$/", $pDelayArr, $ppEnd;
            if ( $pDelayArr == $ppEnd ) {
                $pTempNode = 0;
            }
            else {
                push @NodeList, $pTempNode;
                $pDelayArr += 4;
                $pTempNode = unpack "L", $rt->rget( $pDelayArr, 4 );
            }
        }
        #parse Used after Free node
        my $sys_exception_info_buffer = unpack "Z*", substr( $rt->g('sys_exception_info_buffer'), 0, 22 );
        if ( $sys_exception_info_buffer eq "Debugger_UsedAfterFree" ) {
            return unless $rt->i('rex_core');
            my $rex_core = $rt->g('rex_core');
            my ( $r0, $r1,  $r2,  $r3,  $r4, $r5 ) = unpack( "L6", substr( $rex_core, 12, 4 * 6 ) );
            $pTempNode = $r5 - 20; #sizeof(HNode) is 20
            push @NodeList, $pTempNode;
        }
    }

    my @sortNodeList = sort { $a <=> $b } @NodeList;
    foreach my $pNode (@sortNodeList) {
        my $cci_node_info_size = 16;
        my ( $pLink1, $pLink2, $pLink3, $dwSize, $dwFlag ) = unpack "LLLLL", $rt->rget( $pNode, 4 * 5);

        my $pNodeStruct = $pNode + 20 + $dwSize - 16; #sizeof(NodeStruct)
        my $pNodeStruct1 = $pLink1 + 128; #128 padding size
        my ( $uSig, $uIndex, $pBlock, $uSize ) =unpack "LLLL", $rt->rget( $pNodeStruct, 4 * 4);
        my ( $uSig1, $uIndex1, $pBlock1, $uSize1 ) =unpack "LLLL", $rt->rget( $pNodeStruct1, 4 * 4);
#        printf {$fho} "pNodeStruct:0x%08x pNodeStruct1:0x%08x$/", $pNodeStruct, $pNodeStruct1;

        if ( ($uIndex == 0xBABABABA) && ($uSize > $cci_node_info_size) ) {
            my $uBlockSize = ($uSize - $cci_node_info_size) / 4;
            my $pDataAddr = $pBlock + $cci_node_info_size;
            my $printNode = 1;
            my $p = 0;
            while ( --$uBlockSize > 0 ) {
                my $node_data = unpack "L", $rt->rget( ($pDataAddr+$p), 4 );
                if ( $node_data != 0xFEFEFEFE ) {
                    if ( $printNode == 1 ) {
                        my $pLRAddr = unpack "L", $rt->rget( $pNode + 20 + 4, 4);
                        my $LRsym = $rt->locate_symbol($pLRAddr);
                        printf {$fho} "Node Address: 0x%08x ", $pNode;
                        printf {$fho} "LRAddr:0x%08x LRsym:%s\t", $pLRAddr, pack("A25", $LRsym);
                        print {$fho} "Size:$dwSize$/";
                        $printNode = 0;
                    }
                    printf {$fho} "\t 0x%08x 0x%08x offset:%d$/", ($pDataAddr+$p), $node_data, ($pDataAddr+$p) - $pNode;
                }
                $p += 4;
            }
        }
        elsif ( ($uIndex1 == 0xBABABABA) && ($uSize1 > $cci_node_info_size) ) {
            my $uBlockSize = ($uSize1 - $cci_node_info_size) / 4;
            my $pDataAddr = $pBlock1 + $cci_node_info_size;
            my $printNode = 1;
            my $p = 0;
            while ( --$uBlockSize > 0 ) {
                my $node_data = unpack "L", $rt->rget( ($pDataAddr+$p), 4 );
                if ( $node_data != 0xFEFEFEFE ) {
                    if ( $printNode == 1 ) {
                        my $pLRAddr = unpack "L", $rt->rget( $pNode + 20 + 4, 4);
                        my $LRsym = $rt->locate_symbol($pLRAddr);
                        printf {$fho} "Node Address: 0x%08x ", $pNode;
                        printf {$fho} "LRAddr:0x%08x LRsym:%s\t", $pLRAddr, pack("A25", $LRsym);
                        print {$fho} "Size:$dwSize$/";
                        $printNode = 0;
                    }
                    printf {$fho} "\t 0x%08x 0x%08x offset:%d$/", ($pDataAddr+$p), $node_data, ($pDataAddr+$p) - $pNode;
                }
                $p += 4;
            }
        }
        elsif ( ($uIndex != 0xBABABABA) && ($uIndex1 != 0xBABABABA) ) {
            my $pLRAddr = unpack "L", $rt->rget( $pNode + 20 + 4, 4);
            my $LRsym = $rt->locate_symbol($pLRAddr);
            printf {$fho} "Node Address: 0x%08x ", $pNode;
            print {$fho} "Size:$dwSize";
            printf {$fho} "LRAddr:0x%08x LRsym:%s\t", $pLRAddr, pack("A25", $LRsym);
            printf {$fho} "\tFlag Incorrect:0x%08x\n", $uIndex;
        }
    }
}

sub main {
    my $rd_fn   = shift;
    my $elf_fn  = shift;
    my $r_tasks = shift;
    my $opt_f3hash = shift;

    my $fho = *STDOUT;
    die "Size of $rd_fn < 128MB!" if -s $rd_fn < 128*1024*1024;
    print {$fho} "---Start analyzing ramdump of $rd_fn---\n";
    my $rt = Runtime->new( $rd_fn, $elf_fn );

    print {$fho} "-" x 20, "contents of cci_ex_log_info", "-" x 20, $/;
    print {$fho} join( $/, unpack( "Z80" x 8, $rt->g('cci_ex_log_info') ) ), $/;

    print {$fho} "-" x 20, "contents of qxdm_dbg_msg", "-" x 20, $/;
    print {$fho} unpack( "Z*", $rt->g('qxdm_dbg_msg') ), $/;

    my $ticks = unpack "L", substr( $rt->g('timers'), 36, 4 );
    print {$fho}
      "timers.isr_time = $ticks ticks ~ ",
      int( $ticks / 32768 ), " secs ~ ",
      sprintf( "%.2f", $ticks / 32768 / 60 ), " mins ~ ",
      sprintf( "%.2f", $ticks / 32768 / 60 / 60 ), " hours", $/;

    my $hint = get_info_pos();
    my $rih  = rd_get_info( $rt, $hint );
    my $eih  = elf_get_info( $rt, $hint );

    do_version_info( $rih, $eih, $hint );

    do_Timetick_Info($rt, $fho);
    do_Mem_avail_Info($rt, $fho);

    my $khash = rd_get_ktcb($rt);
    print_ktcb( $khash, $fho );

    do_rd( $rt, $khash, $fho );

    print {$fho} "Getting symbol table from $elf_fn... ";
    print {$fho} "done!\n";

    do_current_call_stack( $rt, $fho );
    do_call_stack( $rt, $khash, $r_tasks, $fho );

    print {$fho} "Getting last frame... ";
    dump_frame_buffer( $rt, $rt->i('mainlcd_buf')->{Value},
        240, 320, "lastframe1.bmp" );
    dump_frame_buffer( $rt, $rt->i('javaLcdBuf')->{Value},
        240, 320, "lastframe-java.bmp" );
    print {$fho} "done saved in lastframe!\n";

#    do_g_asMonitorHdr( $rt, $fho );
#    do_memPoolInfo( $rt, $fho );
    do_OEMHeapInfo( $rt, $fho );
    do_JkCallerInfo( $rt, $fho );

    print {$fho} "Dump GPF Queue Information...\n";
    do_g_Gpf2RexQueuePtrTable( $rt, $fho );
    do_g_Gpf2RexQueueLinkTable( $rt, $fho );
    do_g_Gpf2RexQueueDataTable( $rt, $fho );
    do_g_SpOverflowDetect($rt, $fho);
    do_g_DumpMFWHeapInfo( $rt, $fho );
    do_MFW_GetMaxFreeBlkSizeInfo( $rt, $fho );
    do_g_DumpCCIHeapInfo( $rt, $fho );
    do_SYS_GetMaxFreeBlkSizeInfo( $rt, $fho );
    do_g_DumpGPFHeapInfo( $rt, $fho );
    do_GPF_GetMaxFreeBlkSizeInfo( $rt, $fho );
    do_ShowHeapMaxSizeInfo( $rt, $fho );
    do_ShowIpcMemInfo( $rt, $fho );
    do_DumpJavaTraceBuff( $rt, $fho );
    do_parsePageFaultIP( $rt, $fho );
    do_ArcCallerInfo( $rt, $fho );
    do_MCCallerInfo( $rt, $fho );
    do_ShowHandsetInfo( $rt, $fho );
    do_parseFileHandleInfo( $rt, $fho);
    do_at_time_history( $rt, $fho);
    parse_k1Heap( $rt, $fho);
    parseKeyLog( $rt , $fho );
    checkDelayListData( $rt, $fho );
    do_CCI_PartitionPoolInfo( $rt, $fho );

    if ($opt_f3hash) {
	my $qhash = read_hashfile($opt_f3hash);
	open my $tbfh, ">", "tracebuffer.txt" or die $!,$/;
	dump_amss_trace_buffer($rt,
			       @{$rt->i('trace_buffer')}{qw(Value Size)},
			       unpack("L", $rt->g('trace_buffer_head')),
			       unpack("L", $rt->g('trace_buffer_tail')),
			       unpack("L", $rt->g('diag_debug_trace_record_count')),
			       $qhash,
			       $tbfh,
			   );
	close $tbfh;
    }

    print {$fho} "---End analyzing $rd_fn---\n\n";

    #    print {$fho} "---Address Translation Table---\n";
    #    do_print_address_table($rd_fh, $fho);

    #    close $rd_fh;
    close $fho;
}

print(<<"HELP"), exit 1 unless @ARGV;
usage: $^X $0 ramdump_file elf_file
or
$^X $0 --version ramdump_file
or
$^X $0 --stamp ramdump_file elf_file
or
$^X $0 --task=TASK1 --task=TASK2 ramdump_file elf_file
HELP
$| = 1;    # auto flush
Getopt::Long::Configure("bundling");
Getopt::Long::GetOptions(
    'version' => \my $opt_version,
    'stamp'   => \my $opt_stamp,
    'task=s'  => \my @opt_tasks,
    'f3hash=s'=> \my $opt_f3hash,
);
do_version(@ARGV), exit 0 if $opt_version;
do_stamp(@ARGV),   exit 0 if $opt_stamp;
my $t = Benchmark::timeit( 1, sub { main( @ARGV, \@opt_tasks, $opt_f3hash ) } );

#warn Benchmark::timestr($t),$/;
exit 0 unless eval { require Net::SMTP };
my $to_address = "xxx@xxx";
my $smtp = Net::SMTP->new('swhome');
$smtp->mail( getlogin() );
$smtp->to($to_address);
$smtp->data();
$smtp->datasend( "To: $to_address", $/ );
$smtp->datasend("\n");
$smtp->datasend( "hostname:   ", hostname(),             $/ );
$smtp->datasend( "login:      ", getlogin(),             $/ );
$smtp->datasend( "timeinfo:   ", Benchmark::timestr($t), $/ );
$smtp->datasend( "scriptinfo: ", $0, -s $0, " ", ctime( stat($0)->mtime ), $/ );
$smtp->datasend( sprintf "perlver: v%vd$/", $^V );
$smtp->dataend();
$smtp->quit;

__DATA__
pmi_stamp                                0x00300104   
ver_sw                                   0x00300168   
ver_sw2                                  0x00300174   
ver_hw                                   0x00300180   
ver_software                             0x00300190   
ver_qct                                  0x0030019c   
IMEI_SVN                                 0x003001a4   
ver_foxcat                               0x003001a8   
sw_build_date                            0x003001ac   
pmi_stamp2                               0x003001ac   
