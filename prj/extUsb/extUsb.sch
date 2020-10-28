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
L Device:R R2
U 1 1 5F99AD9D
P 8500 5500
F 0 "R2" V 8400 5450 50  0000 C CNN
F 1 "68" V 8500 5500 50  0000 C CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 8430 5500 50  0001 C CNN
F 3 "~" H 8500 5500 50  0001 C CNN
	1    8500 5500
	0    1    1    0   
$EndComp
$Comp
L Device:R R3
U 1 1 5F99B134
P 8500 5700
F 0 "R3" V 8600 5650 50  0000 C CNN
F 1 "68" V 8500 5700 50  0000 C CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 8430 5700 50  0001 C CNN
F 3 "~" H 8500 5700 50  0001 C CNN
	1    8500 5700
	0    1    1    0   
$EndComp
$Comp
L Device:R R1
U 1 1 5F99B487
P 7950 5350
F 0 "R1" H 8000 5400 50  0000 L CNN
F 1 "1k5" V 7950 5300 50  0000 L CNN
F 2 "Resistor_SMD:R_0603_1608Metric_Pad0.98x0.95mm_HandSolder" V 7880 5350 50  0001 C CNN
F 3 "~" H 7950 5350 50  0001 C CNN
F 4 "R" H 7950 5350 50  0001 C CNN "Spice_Primitive"
F 5 "" H 7950 5350 50  0001 C CNN "Spice_Model"
F 6 "Y" H 7950 5350 50  0001 C CNN "Spice_Netlist_Enabled"
	1    7950 5350
	1    0    0    -1  
$EndComp
NoConn ~ 7100 5700
$Comp
L power:GND #PWR01
U 1 1 5F99B78B
P 7050 5950
F 0 "#PWR01" H 7050 5700 50  0001 C CNN
F 1 "GND" H 7055 5777 50  0000 C CNN
F 2 "" H 7050 5950 50  0001 C CNN
F 3 "" H 7050 5950 50  0001 C CNN
	1    7050 5950
	1    0    0    -1  
$EndComp
$Comp
L Connector:USB_B_Micro J1
U 1 1 5F998976
P 7150 5500
F 0 "J1" H 6920 5397 50  0000 R CNN
F 1 "USB_B_Micro" H 7350 5850 50  0000 R CNN
F 2 "Connector_USB:USB_Micro-B_Molex-105017-0001" H 7300 5450 50  0001 C CNN
F 3 "~" H 7300 5450 50  0001 C CNN
	1    7150 5500
	1    0    0    -1  
$EndComp
$Comp
L power:GND #PWR02
U 1 1 5F9A2222
P 9150 6150
F 0 "#PWR02" H 9150 5900 50  0001 C CNN
F 1 "GND" H 9155 5977 50  0000 C CNN
F 2 "" H 9150 6150 50  0001 C CNN
F 3 "" H 9150 6150 50  0001 C CNN
	1    9150 6150
	1    0    0    -1  
$EndComp
NoConn ~ 7450 5700
Wire Wire Line
	9150 6100 9150 6150
Wire Wire Line
	7050 5900 7050 5950
Wire Wire Line
	7150 5900 7150 5950
Wire Wire Line
	7150 5950 7050 5950
Connection ~ 7050 5950
Wire Wire Line
	8650 5700 8750 5700
Wire Wire Line
	7950 5600 7950 5700
Wire Wire Line
	7950 5700 8300 5700
Wire Wire Line
	7450 5300 7450 5100
Wire Wire Line
	7950 5200 7950 5100
Wire Wire Line
	7950 5100 9050 5100
$Comp
L power:GND #PWR03
U 1 1 5F9ABD67
P 10750 5850
F 0 "#PWR03" H 10750 5600 50  0001 C CNN
F 1 "GND" H 10755 5677 50  0000 C CNN
F 2 "" H 10750 5850 50  0001 C CNN
F 3 "" H 10750 5850 50  0001 C CNN
	1    10750 5850
	1    0    0    -1  
$EndComp
Wire Wire Line
	10750 5800 10750 5850
$Comp
L Connector_Generic:Conn_01x05 J2
U 1 1 5F9A8B50
P 10950 5600
F 0 "J2" H 10868 5175 50  0000 C CNN
F 1 "Conn_01x05" H 10868 5266 50  0000 C CNN
F 2 "Connector_PinHeader_2.54mm:PinHeader_1x05_P2.54mm_Horizontal" H 10950 5600 50  0001 C CNN
F 3 "~" H 10950 5600 50  0001 C CNN
	1    10950 5600
	1    0    0    1   
$EndComp
$Comp
L Logic_LevelTranslator:SN74LVC2T45DCUR U1
U 1 1 5F998087
P 9150 5600
F 0 "U1" H 9150 4919 50  0000 C CNN
F 1 "SN74LVC2T45" H 9150 5150 50  0000 C CNN
F 2 "Package_SO:SSOP-8_2.95x2.8mm_P0.65mm" H 9200 5050 50  0001 C CNN
F 3 "http://www.ti.com/lit/ds/symlink/sn74lvc2t45.pdf" H 8250 5050 50  0001 C CNN
	1    9150 5600
	-1   0    0    -1  
$EndComp
Text GLabel 10700 5600 0    50   BiDi ~ 0
Vext
Text GLabel 9600 5100 2    50   BiDi ~ 0
Vext
Text GLabel 9600 5500 2    50   BiDi ~ 0
pin_usb_p
Text GLabel 9600 5700 2    50   BiDi ~ 0
pin_usb_n
Text GLabel 9600 5900 2    50   BiDi ~ 0
pin_usb_oe
Text GLabel 10700 5500 0    50   BiDi ~ 0
pin_usb_p
Text GLabel 10700 5400 0    50   BiDi ~ 0
pin_usb_n
Text GLabel 10700 5700 0    50   BiDi ~ 0
pin_usb_oe
Wire Wire Line
	9250 5100 9600 5100
Wire Wire Line
	9550 5500 9600 5500
Wire Wire Line
	9550 5700 9600 5700
Wire Wire Line
	9550 5900 9600 5900
Wire Wire Line
	10750 5400 10700 5400
Wire Wire Line
	10700 5500 10750 5500
Wire Wire Line
	10700 5600 10750 5600
Wire Wire Line
	10700 5700 10750 5700
Text GLabel 7450 5050 1    50   BiDi ~ 0
Vusb
Text GLabel 8300 5750 3    50   BiDi ~ 0
usb_n
Text GLabel 8300 5450 1    50   BiDi ~ 0
usb_p
Wire Wire Line
	8750 5500 8650 5500
Wire Wire Line
	7450 5600 7950 5600
Wire Wire Line
	7950 5500 8300 5500
Wire Wire Line
	8300 5450 8300 5500
Connection ~ 8300 5500
Wire Wire Line
	8300 5500 8350 5500
Wire Wire Line
	7450 5500 7950 5500
Connection ~ 7950 5500
Wire Wire Line
	7450 5050 7450 5100
Connection ~ 7450 5100
Wire Wire Line
	7450 5100 7950 5100
Connection ~ 7950 5100
Wire Wire Line
	8300 5750 8300 5700
Connection ~ 8300 5700
Wire Wire Line
	8300 5700 8350 5700
$EndSCHEMATC
