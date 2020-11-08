EESchema Schematic File Version 4
EELAYER 30 0
EELAYER END
$Descr A4 11693 8268
encoding utf-8
Sheet 1 1
Title ""
Date ""
Rev ""
Comp ""
Comment1 ""
Comment2 ""
Comment3 ""
Comment4 ""
$EndDescr
$Comp
L Device:R R1
U 1 1 5F99AD9D
P 2000 6100
F 0 "R1" V 2100 6150 50  0000 C CNN
F 1 "33" V 2000 6050 50  0000 C CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 1930 6100 50  0001 C CNN
F 3 "~" H 2000 6100 50  0001 C CNN
	1    2000 6100
	0    1    1    0   
$EndComp
$Comp
L Device:R R2
U 1 1 5F99B134
P 2000 6700
F 0 "R2" V 2100 6750 50  0000 C CNN
F 1 "33" V 2000 6650 50  0000 C CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 1930 6700 50  0001 C CNN
F 3 "~" H 2000 6700 50  0001 C CNN
	1    2000 6700
	0    1    1    0   
$EndComp
$Comp
L Device:R R3
U 1 1 5F99B487
P 1700 5650
F 0 "R3" H 1750 5600 50  0000 L CNN
F 1 "1k5" V 1700 5550 50  0000 L CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 1630 5650 50  0001 C CNN
F 3 "~" H 1700 5650 50  0001 C CNN
F 4 "R" H 1700 5650 50  0001 C CNN "Spice_Primitive"
F 5 "" H 1700 5650 50  0001 C CNN "Spice_Model"
F 6 "Y" H 1700 5650 50  0001 C CNN "Spice_Netlist_Enabled"
	1    1700 5650
	1    0    0    -1  
$EndComp
$Comp
L Connector:USB_B_Micro J1
U 1 1 5F998976
P 1350 2000
F 0 "J1" H 1120 1897 50  0000 R CNN
F 1 "USB_B_Micro" H 1550 2350 50  0000 R CNN
F 2 "Connector_USB:USB_Micro-B_Molex-105017-0001" H 1500 1950 50  0001 C CNN
F 3 "https://www.molex.com/pdm_docs/sd/1050170001_sd.pdf" H 1500 1950 50  0001 C CNN
	1    1350 2000
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR02
U 1 1 5F9A2222
P 2600 6750
F 0 "#PWR02" H 2600 6500 50  0001 C CNN
F 1 "GND" H 2605 6577 50  0000 C CNN
F 2 "" H 2600 6750 50  0001 C CNN
F 3 "" H 2600 6750 50  0001 C CNN
	1    2600 6750
	1    0    0    -1  
$EndComp
NoConn ~ 1650 2200
Wire Wire Line
	2600 6700 2600 6750
Wire Wire Line
	1250 2400 1250 2450
$Comp
L power:GND #PWR03
U 1 1 5F9ABD67
P 10150 5750
F 0 "#PWR03" H 10150 5500 50  0001 C CNN
F 1 "GND" H 10155 5577 50  0000 C CNN
F 2 "" H 10150 5750 50  0001 C CNN
F 3 "" H 10150 5750 50  0001 C CNN
	1    10150 5750
	1    0    0    -1  
$EndComp
Wire Wire Line
	10150 5700 10150 5750
$Comp
L Connector_Generic:Conn_01x05 J2
U 1 1 5F9A8B50
P 10350 5500
F 0 "J2" H 10268 5075 50  0000 C CNN
F 1 "Conn_01x05" H 10268 5166 50  0000 C CNN
F 2 "Connector_PinHeader_2.54mm:PinHeader_1x05_P2.54mm_Horizontal" H 10350 5500 50  0001 C CNN
F 3 "~" H 10350 5500 50  0001 C CNN
	1    10350 5500
	1    0    0    1   
$EndComp
Text GLabel 10100 5600 0    50   BiDi ~ 0
Vext
Text GLabel 3500 5450 2    50   BiDi ~ 0
Vext
Text GLabel 3750 6100 2    50   BiDi ~ 0
pin_usb_p
Text GLabel 4250 6300 2    50   BiDi ~ 0
pin_usb_n
Text GLabel 3750 6500 2    50   BiDi ~ 0
pin_usb_oe
Text GLabel 10100 5500 0    50   BiDi ~ 0
pin_usb_p
Text GLabel 10100 5400 0    50   BiDi ~ 0
pin_usb_n
Text GLabel 10100 5300 0    50   BiDi ~ 0
pin_usb_oe
Wire Wire Line
	10150 5300 10100 5300
Wire Wire Line
	10100 5400 10150 5400
Wire Wire Line
	10100 5500 10150 5500
Wire Wire Line
	10100 5600 10150 5600
Text GLabel 1300 6700 0    50   BiDi ~ 0
usb_n
Text GLabel 1300 6100 0    50   BiDi ~ 0
usb_p
Text GLabel 1650 2000 2    50   BiDi ~ 0
usb_p
Text GLabel 1650 2100 2    50   BiDi ~ 0
usb_n
$Comp
L Device:C C5
U 1 1 5F9CE4ED
P 2200 1950
F 0 "C5" H 2300 1950 50  0000 L CNN
F 1 "10u" H 2200 1850 50  0000 L CNN
F 2 "Capacitor_SMD:C_0603_1608Metric_Pad1.08x0.95mm_HandSolder" H 2238 1800 50  0001 C CNN
F 3 "~" H 2200 1950 50  0001 C CNN
	1    2200 1950
	1    0    0    -1  
$EndComp
Wire Wire Line
	1350 2450 1250 2450
Wire Wire Line
	1350 2400 1350 2450
Connection ~ 2200 1800
$Comp
L power:+5V #PWR04
U 1 1 5F9ECE67
P 2200 1800
F 0 "#PWR04" H 2200 1650 50  0001 C CNN
F 1 "+5V" H 2215 1973 50  0000 C CNN
F 2 "" H 2200 1800 50  0001 C CNN
F 3 "" H 2200 1800 50  0001 C CNN
	1    2200 1800
	1    0    0    -1  
$EndComp
$Comp
L Regulator_Linear:MIC5504-3.3YM5 U2
U 1 1 5F9C5271
P 2900 1900
F 0 "U2" H 2900 2267 50  0000 C CNN
F 1 "MIC5504-3.3YM5" H 2900 2176 50  0000 C CNN
F 2 "Package_TO_SOT_SMD:SOT-23-5_HandSoldering" H 2900 1500 50  0001 C CNN
F 3 "http://ww1.microchip.com/downloads/en/DeviceDoc/MIC550X.pdf" H 2650 2150 50  0001 C CNN
	1    2900 1900
	1    0    0    -1  
$EndComp
Wire Wire Line
	2500 1800 2500 2000
$Comp
L Device:C C4
U 1 1 5F9D1CBC
P 3550 1950
F 0 "C4" H 3650 1950 50  0000 L CNN
F 1 "100n" H 3550 1850 50  0000 L CNN
F 2 "Capacitor_SMD:C_0603_1608Metric_Pad1.08x0.95mm_HandSolder" H 3588 1800 50  0001 C CNN
F 3 "~" H 3550 1950 50  0001 C CNN
	1    3550 1950
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR06
U 1 1 5F9DB4B7
P 2900 2450
F 0 "#PWR06" H 2900 2200 50  0001 C CNN
F 1 "GND" H 2905 2277 50  0000 C CNN
F 2 "" H 2900 2450 50  0001 C CNN
F 3 "" H 2900 2450 50  0001 C CNN
	1    2900 2450
	1    0    0    -1  
$EndComp
Connection ~ 3550 1800
$Comp
L power:+3.3V #PWR08
U 1 1 5F9E8D54
P 3550 1800
F 0 "#PWR08" H 3550 1650 50  0001 C CNN
F 1 "+3.3V" H 3565 1973 50  0000 C CNN
F 2 "" H 3550 1800 50  0001 C CNN
F 3 "" H 3550 1800 50  0001 C CNN
	1    3550 1800
	1    0    0    -1  
$EndComp
Connection ~ 2500 1800
Wire Wire Line
	1350 2450 2200 2450
Connection ~ 1350 2450
Wire Wire Line
	2900 2200 2900 2450
Connection ~ 2900 2450
Wire Wire Line
	2200 2100 2200 2450
Connection ~ 2200 2450
Wire Wire Line
	2200 2450 2900 2450
Wire Wire Line
	3550 2100 3550 2450
Wire Wire Line
	3550 2450 2900 2450
$Comp
L power:+3.3V #PWR05
U 1 1 5F9FCC4B
P 2500 5700
F 0 "#PWR05" H 2500 5550 50  0001 C CNN
F 1 "+3.3V" H 2515 5873 50  0000 C CNN
F 2 "" H 2500 5700 50  0001 C CNN
F 3 "" H 2500 5700 50  0001 C CNN
	1    2500 5700
	1    0    0    -1  
$EndComp
Wire Wire Line
	1850 6100 1700 6100
Wire Wire Line
	2150 6100 2200 6100
$Comp
L power:+3.3V #PWR01
U 1 1 5FA00B0B
P 1050 5000
F 0 "#PWR01" H 1050 4850 50  0001 C CNN
F 1 "+3.3V" H 1065 5173 50  0000 C CNN
F 2 "" H 1050 5000 50  0001 C CNN
F 3 "" H 1050 5000 50  0001 C CNN
	1    1050 5000
	1    0    0    -1  
$EndComp
$Comp
L Device:C C3
U 1 1 5FA02226
P 3400 5600
F 0 "C3" H 3500 5600 50  0000 L CNN
F 1 "100n" H 3400 5500 50  0000 L CNN
F 2 "Capacitor_SMD:C_0603_1608Metric_Pad1.08x0.95mm_HandSolder" H 3438 5450 50  0001 C CNN
F 3 "~" H 3400 5600 50  0001 C CNN
	1    3400 5600
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR07
U 1 1 5FA05015
P 3400 5750
F 0 "#PWR07" H 3400 5500 50  0001 C CNN
F 1 "GND" H 3405 5577 50  0000 C CNN
F 2 "" H 3400 5750 50  0001 C CNN
F 3 "" H 3400 5750 50  0001 C CNN
	1    3400 5750
	1    0    0    -1  
$EndComp
Wire Wire Line
	2700 5450 2700 5700
$Comp
L Device:C C1
U 1 1 5FA1C049
P 1700 6250
F 0 "C1" H 1800 6250 50  0000 L CNN
F 1 "18p" H 1700 6150 50  0000 L CNN
F 2 "Capacitor_SMD:C_0603_1608Metric_Pad1.08x0.95mm_HandSolder" H 1738 6100 50  0001 C CNN
F 3 "~" H 1700 6250 50  0001 C CNN
	1    1700 6250
	1    0    0    -1  
$EndComp
$Comp
L Device:C C2
U 1 1 5FA1CC20
P 1700 6850
F 0 "C2" H 1800 6850 50  0000 L CNN
F 1 "18p" H 1700 6750 50  0000 L CNN
F 2 "Capacitor_SMD:C_0603_1608Metric_Pad1.08x0.95mm_HandSolder" H 1738 6700 50  0001 C CNN
F 3 "~" H 1700 6850 50  0001 C CNN
	1    1700 6850
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR0101
U 1 1 5FA1D04B
P 1700 7000
F 0 "#PWR0101" H 1700 6750 50  0001 C CNN
F 1 "GND" H 1705 6827 50  0000 C CNN
F 2 "" H 1700 7000 50  0001 C CNN
F 3 "" H 1700 7000 50  0001 C CNN
	1    1700 7000
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR0102
U 1 1 5FA1ECAC
P 1700 6400
F 0 "#PWR0102" H 1700 6150 50  0001 C CNN
F 1 "GND" H 1705 6227 50  0000 C CNN
F 2 "" H 1700 6400 50  0001 C CNN
F 3 "" H 1700 6400 50  0001 C CNN
	1    1700 6400
	1    0    0    -1  
$EndComp
Wire Wire Line
	3500 5450 3400 5450
Connection ~ 3400 5450
Wire Wire Line
	2150 6700 2200 6700
Wire Wire Line
	2200 6700 2200 6300
Connection ~ 1700 6100
Connection ~ 1700 6700
Wire Wire Line
	1700 6700 1850 6700
$Comp
L Logic_LevelTranslator:SN74LVC2T45DCUR U1
U 1 1 5F998087
P 2600 6200
F 0 "U1" H 2800 5850 50  0000 C CNN
F 1 "SN74LVC2T45" H 2600 6200 50  0000 C CNN
F 2 "Package_SO:SSOP-8_2.95x2.8mm_P0.65mm" H 2650 5650 50  0001 C CNN
F 3 "http://www.ti.com/lit/ds/symlink/sn74lvc2t45.pdf" H 1700 5650 50  0001 C CNN
	1    2600 6200
	-1   0    0    -1  
$EndComp
$Comp
L Device:Ferrite_Bead FB1
U 1 1 5FA2AD34
P 1800 1800
F 0 "FB1" V 1526 1800 50  0000 C CNN
F 1 "Ferrite_Bead" V 1617 1800 50  0000 C CNN
F 2 "Inductor_SMD:L_0603_1608Metric_Pad1.05x0.95mm_HandSolder" V 1730 1800 50  0001 C CNN
F 3 "~" H 1800 1800 50  0001 C CNN
	1    1800 1800
	0    1    1    0   
$EndComp
Wire Wire Line
	1950 1800 2200 1800
$Comp
L Device:R R4
U 1 1 5FA4650C
P 1000 5550
F 0 "R4" H 1050 5500 50  0000 L CNN
F 1 "10k" V 1000 5450 50  0000 L CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 930 5550 50  0001 C CNN
F 3 "~" H 1000 5550 50  0001 C CNN
	1    1000 5550
	1    0    0    -1  
$EndComp
Text GLabel 950  5400 0    50   Input ~ 0
Vext
$Comp
L power:GND #PWR0103
U 1 1 5FA4C220
P 1000 5700
F 0 "#PWR0103" H 1000 5450 50  0001 C CNN
F 1 "GND" H 1005 5527 50  0000 C CNN
F 2 "" H 1000 5700 50  0001 C CNN
F 3 "" H 1000 5700 50  0001 C CNN
	1    1000 5700
	1    0    0    -1  
$EndComp
Wire Wire Line
	1700 5800 1700 6100
Wire Wire Line
	950  5400 1000 5400
Connection ~ 1000 5400
Wire Wire Line
	1000 5400 1050 5400
Text Notes 1000 4800 0    50   ~ 0
R3 pullup to 3.3V indicates USB-FullSpeed to host, enabled by connecting Vext.\nWhen Vext is unconnected, R4 pulldown on U3 disables the R3 pullup, indicating "no device" to host.
Text Notes 1000 7450 0    50   ~ 0
R1 and R2 series termination protect D+,D- transmission lines against device-to-host transient voltage spikes.\nOptionally (with C1,C2) include low-pass filtering.
Text Notes 1000 1350 0    50   ~ 0
FB1 blocks noise from propagating to USB host power supply,\nand works in conjunction with C5 to stabilize +5V.\nC3, C4, and C5 bypass capacitors stabilize power supplies.\nU2 provides 3.3V, as required by USB.
Text Notes 10500 6150 2    50   ~ 0
J2 separated via labels to simplify pin re-assignment.
Text Notes 7000 6700 0    50   ~ 0
Levelshifter for low or unknown voltage (1.65V..5.5V) logic implementing USB Full Speed protocol.\nFor example, FPGA with protocol implemented in logic, or a MCU bit-banging the protocol.
Text Notes 7400 7500 0    50   ~ 0
extUsb
Text Notes 8150 7650 0    50   ~ 0
2020-10-31
Text Notes 10600 7650 0    50   ~ 0
1.0.0
Wire Wire Line
	1450 5600 1450 5700
Wire Wire Line
	1450 5700 1000 5700
Connection ~ 1000 5700
Wire Wire Line
	1050 5300 1050 5000
Wire Wire Line
	1050 5000 1450 5000
Connection ~ 1050 5000
Wire Wire Line
	1650 5300 1700 5300
Wire Wire Line
	1700 5300 1700 5500
$Comp
L Analog_Switch:TS5A3166DBVR U3
U 1 1 5FA73056
P 1350 5300
F 0 "U3" H 1250 5450 50  0000 L CNN
F 1 "TS5A3166DBVR" H 1150 5200 50  0000 L CNN
F 2 "Package_TO_SOT_SMD:SOT-23-5_HandSoldering" H 1300 5150 50  0001 C CNN
F 3 " http://www.ti.com/lit/ds/symlink/ts5a3166.pdf" H 1350 5400 50  0001 C CNN
	1    1350 5300
	1    0    0    -1  
$EndComp
Wire Wire Line
	3400 5450 3050 5450
Wire Wire Line
	3300 1800 3550 1800
Wire Wire Line
	2200 1800 2500 1800
$Comp
L Connector:TestPoint TP2
U 1 1 5FA881AA
P 4250 6300
F 0 "TP2" H 4308 6418 50  0000 L CNN
F 1 "TestPoint" H 4308 6327 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 4450 6300 50  0001 C CNN
F 3 "~" H 4450 6300 50  0001 C CNN
	1    4250 6300
	1    0    0    -1  
$EndComp
$Comp
L Connector:TestPoint TP1
U 1 1 5FA87D46
P 3750 6100
F 0 "TP1" H 3808 6218 50  0000 L CNN
F 1 "TestPoint" H 3808 6127 50  0000 L CNN
F 2 "" H 3950 6100 50  0001 C CNN
F 3 "~" H 3950 6100 50  0001 C CNN
	1    3750 6100
	1    0    0    -1  
$EndComp
Wire Wire Line
	3000 6100 3750 6100
Wire Wire Line
	1300 6700 1700 6700
Wire Wire Line
	1300 6100 1700 6100
Wire Wire Line
	3000 6300 4250 6300
$Comp
L Connector:TestPoint TP4
U 1 1 5FAA3783
P 10100 3900
F 0 "TP4" H 10158 4018 50  0000 L CNN
F 1 "TestPoint" H 10158 3927 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 10300 3900 50  0001 C CNN
F 3 "~" H 10300 3900 50  0001 C CNN
	1    10100 3900
	1    0    0    -1  
$EndComp
$Comp
L Connector:TestPoint TP5
U 1 1 5FAA3DCC
P 10100 4150
F 0 "TP5" H 10158 4268 50  0000 L CNN
F 1 "TestPoint" H 10158 4177 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 10300 4150 50  0001 C CNN
F 3 "~" H 10300 4150 50  0001 C CNN
	1    10100 4150
	1    0    0    -1  
$EndComp
$Comp
L Connector:TestPoint TP6
U 1 1 5FAA4E02
P 10100 4400
F 0 "TP6" H 10158 4518 50  0000 L CNN
F 1 "TestPoint" H 10158 4427 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 10300 4400 50  0001 C CNN
F 3 "~" H 10300 4400 50  0001 C CNN
	1    10100 4400
	1    0    0    -1  
$EndComp
$Comp
L Connector:TestPoint TP3
U 1 1 5FAA52CF
P 3750 6500
F 0 "TP3" H 3808 6618 50  0000 L CNN
F 1 "TestPoint" H 3808 6527 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 3950 6500 50  0001 C CNN
F 3 "~" H 3950 6500 50  0001 C CNN
	1    3750 6500
	1    0    0    -1  
$EndComp
Wire Wire Line
	3000 6500 3750 6500
$Comp
L power:GND #PWR0104
U 1 1 5FAA8E6F
P 10000 4400
F 0 "#PWR0104" H 10000 4150 50  0001 C CNN
F 1 "GND" H 10005 4227 50  0000 C CNN
F 2 "" H 10000 4400 50  0001 C CNN
F 3 "" H 10000 4400 50  0001 C CNN
	1    10000 4400
	1    0    0    -1  
$EndComp
Wire Wire Line
	10000 4400 10100 4400
Wire Wire Line
	10000 4400 10000 4150
Wire Wire Line
	10000 3900 10100 3900
Connection ~ 10000 4400
Wire Wire Line
	10100 4150 10000 4150
Connection ~ 10000 4150
Wire Wire Line
	10000 4150 10000 3900
$Comp
L Connector:TestPoint TP7
U 1 1 5FAB2342
P 3050 5450
F 0 "TP7" H 3108 5568 50  0000 L CNN
F 1 "TestPoint" H 3108 5477 50  0000 L CNN
F 2 "TestPoint:TestPoint_Pad_D2.0mm" H 3250 5450 50  0001 C CNN
F 3 "~" H 3250 5450 50  0001 C CNN
	1    3050 5450
	1    0    0    -1  
$EndComp
Connection ~ 3050 5450
Wire Wire Line
	3050 5450 2700 5450
$EndSCHEMATC
