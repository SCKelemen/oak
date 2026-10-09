import Oak.ArmDecoderClassification.Batch000
import Oak.ArmDecoderClassification.Batch001
import Oak.ArmDecoderClassification.Batch002
import Oak.ArmDecoderClassification.Batch003
import Oak.ArmDecoderClassification.Batch004
import Oak.ArmDecoderClassification.Batch005
import Oak.ArmDecoderClassification.Batch006
import Oak.ArmDecoderClassification.Batch007
import Oak.ArmDecoderClassification.Batch008
import Oak.ArmDecoderClassification.Batch009
import Oak.ArmDecoderClassification.Batch010
import Oak.ArmDecoderClassification.Batch011
import Oak.ArmDecoderClassification.Batch012
import Oak.ArmDecoderClassification.Batch013
import Oak.ArmDecoderClassification.Batch014
import Oak.ArmDecoderClassification.Batch015
import Oak.ArmDecoderClassification.Batch016
import Oak.ArmDecoderClassification.Batch017
import Oak.ArmDecoderClassification.Batch018
import Oak.ArmDecoderClassification.Batch019
import Oak.ArmDecoderClassification.Batch020
import Oak.ArmDecoderClassification.Batch021
import Oak.ArmDecoderClassification.Batch022
import Oak.ArmDecoderClassification.Batch023
import Oak.ArmDecoderClassification.Batch024
import Oak.ArmDecoderClassification.Batch025
import Oak.ArmDecoderClassification.Batch026
import Oak.ArmDecoderClassification.Batch027
import Oak.ArmDecoderClassification.Batch028
import Oak.ArmDecoderClassification.Batch029
import Oak.ArmDecoderClassification.Batch030
import Oak.ArmDecoderClassification.Batch031
import Oak.ArmDecoderClassification.Batch032
import Oak.ArmDecoderClassification.Batch033
import Oak.ArmDecoderClassification.Batch034
import Oak.ArmDecoderClassification.Batch035
import Oak.ArmDecoderClassification.Batch036
import Oak.ArmDecoderClassification.Batch037
import Oak.ArmDecoderClassification.Batch038
import Oak.ArmDecoderClassification.Batch039
import Oak.ArmDecoderClassification.Batch040
import Oak.ArmDecoderClassification.Batch041
import Oak.ArmDecoderClassification.Batch042
import Oak.ArmDecoderClassification.Batch043
import Oak.ArmDecoderClassification.Batch044
import Oak.ArmDecoderClassification.Batch045
import Oak.ArmDecoderClassification.Batch046
import Oak.ArmDecoderClassification.Batch047
import Oak.ArmDecoderClassification.Batch048
import Oak.ArmDecoderClassification.Batch049
import Oak.ArmDecoderClassification.Batch050
import Oak.ArmDecoderClassification.Batch051
import Oak.ArmDecoderClassification.Batch052
import Oak.ArmDecoderClassification.Batch053
import Oak.ArmDecoderClassification.Batch054
import Oak.ArmDecoderClassification.Batch055
import Oak.ArmDecoderClassification.Batch056
import Oak.ArmDecoderClassification.Batch057
import Oak.ArmDecoderClassification.Batch058
import Oak.ArmDecoderClassification.Batch059
import Oak.ArmDecoderClassification.Batch060
import Oak.ArmDecoderClassification.Batch061
import Oak.ArmDecoderClassification.Batch062
import Oak.ArmDecoderClassification.Batch063
import Oak.ArmDecoderClassification.Batch064
import Oak.ArmDecoderClassification.Batch065
import Oak.ArmDecoderClassification.Batch066
import Oak.ArmDecoderClassification.Batch067
import Oak.ArmDecoderClassification.Batch068
import Oak.ArmDecoderClassification.Batch069
import Oak.ArmDecoderClassification.Batch070
import Oak.ArmDecoderClassification.Batch071
import Oak.ArmDecoderClassification.Batch072
import Oak.ArmDecoderClassification.Batch073
import Oak.ArmDecoderClassification.Batch074
import Oak.ArmDecoderClassification.Batch075
import Oak.ArmDecoderClassification.Batch076
import Oak.ArmDecoderClassification.Batch077
import Oak.ArmDecoderClassification.Batch078
import Oak.ArmDecoderClassification.Batch079
import Oak.ArmDecoderClassification.Batch080
import Oak.ArmDecoderClassification.Batch081
import Oak.ArmDecoderClassification.Batch082
import Oak.ArmDecoderClassification.Batch083
import Oak.ArmDecoderClassification.Batch084
import Oak.ArmDecoderClassification.Batch085
import Oak.ArmDecoderClassification.Batch086
import Oak.ArmDecoderClassification.Batch087
import Oak.ArmDecoderClassification.Batch088
import Oak.ArmDecoderClassification.Batch089
import Oak.ArmDecoderClassification.Batch090
import Oak.ArmDecoderClassification.Batch091
import Oak.ArmDecoderClassification.Batch092
import Oak.ArmDecoderClassification.Batch093
import Oak.ArmDecoderClassification.Batch094
import Oak.ArmDecoderClassification.Batch095
import Oak.ArmDecoderClassification.Batch096
import Oak.ArmDecoderClassification.Batch097
import Oak.ArmDecoderClassification.Batch098
import Oak.ArmDecoderClassification.Batch099
import Oak.ArmDecoderClassification.Batch100
import Oak.ArmDecoderClassification.Batch101
import Oak.ArmDecoderClassification.Batch102
import Oak.ArmDecoderClassification.Batch103
import Oak.ArmDecoderClassification.Batch104
import Oak.ArmDecoderClassification.Batch105
import Oak.ArmDecoderClassification.Batch106
import Oak.ArmDecoderClassification.Batch107
import Oak.ArmDecoderClassification.Batch108
import Oak.ArmDecoderClassification.Batch109
import Oak.ArmDecoderClassification.Batch110
import Oak.ArmDecoderClassification.Batch111
import Oak.ArmDecoderClassification.Batch112
import Oak.ArmDecoderClassification.Batch113
import Oak.ArmDecoderClassification.Batch114

namespace Oak.ArmDecoderClassification
open Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Composes already checked batches without normalizing their raw source again. -/
structure Batch where
  entries : List CheckedRow
  rows : List Row
  bound : entries.map CheckedRow.row = rows
  indexList : List Nat
  indices_bound : rows.map Row.index = indexList
  andMatches : List Nat
  and_bound : choices rows 0x0a010000#32 (-1) = andMatches
  orrMatches : List Nat
  orr_bound : choices rows 0x2a010000#32 (-1) = orrMatches
  eorMatches : List Nat
  eor_bound : choices rows 0x4a010000#32 (-1) = eorMatches
  retMatches : List Nat
  ret_bound : choices rows 0xd65f03c0#32 (-1) = retMatches

inductive Word where | and | orr | eor | ret

def Word.bits : Word → BitVec 32
  | .and => 0x0a010000 | .orr => 0x2a010000 | .eor => 0x4a010000 | .ret => 0xd65f03c0

def Batch.matches (b : Batch) : Word → List Nat
  | .and => b.andMatches | .orr => b.orrMatches | .eor => b.eorMatches | .ret => b.retMatches

theorem Batch.proved (b : Batch) (w : Word) : choices b.rows w.bits (-1) = b.matches w := by
  cases w with
  | and => exact b.and_bound
  | orr => exact b.orr_bound
  | eor => exact b.eor_bound
  | ret => exact b.ret_bound

theorem choices_flatMap (bs : List Batch) (word : BitVec 32) (see : Int) :
    choices (bs.flatMap Batch.rows) word see = bs.flatMap (fun b => choices b.rows word see) := by
  simp only [choices, List.filter_flatMap, List.map_flatMap]

def batch0 : Batch := ⟨entries0, rows0, bound0, [1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033], indices0, [], choices_and_0, [], choices_orr_0, [], choices_eor_0, [], choices_ret_0⟩
def batch1 : Batch := ⟨entries1, rows1, bound1, [1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041], indices1, [], choices_and_1, [], choices_orr_1, [], choices_eor_1, [], choices_ret_1⟩
def batch2 : Batch := ⟨entries2, rows2, bound2, [1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049], indices2, [], choices_and_2, [], choices_orr_2, [], choices_eor_2, [], choices_ret_2⟩
def batch3 : Batch := ⟨entries3, rows3, bound3, [1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057], indices3, [], choices_and_3, [], choices_orr_3, [], choices_eor_3, [], choices_ret_3⟩
def batch4 : Batch := ⟨entries4, rows4, bound4, [1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065], indices4, [], choices_and_4, [], choices_orr_4, [], choices_eor_4, [], choices_ret_4⟩
def batch5 : Batch := ⟨entries5, rows5, bound5, [1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073], indices5, [], choices_and_5, [], choices_orr_5, [], choices_eor_5, [], choices_ret_5⟩
def batch6 : Batch := ⟨entries6, rows6, bound6, [1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081], indices6, [], choices_and_6, [], choices_orr_6, [], choices_eor_6, [], choices_ret_6⟩
def batch7 : Batch := ⟨entries7, rows7, bound7, [1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089], indices7, [], choices_and_7, [], choices_orr_7, [], choices_eor_7, [], choices_ret_7⟩
def batch8 : Batch := ⟨entries8, rows8, bound8, [1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097], indices8, [], choices_and_8, [], choices_orr_8, [], choices_eor_8, [], choices_ret_8⟩
def batch9 : Batch := ⟨entries9, rows9, bound9, [1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105], indices9, [], choices_and_9, [], choices_orr_9, [], choices_eor_9, [], choices_ret_9⟩
def batch10 : Batch := ⟨entries10, rows10, bound10, [1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113], indices10, [], choices_and_10, [], choices_orr_10, [], choices_eor_10, [], choices_ret_10⟩
def batch11 : Batch := ⟨entries11, rows11, bound11, [1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121], indices11, [], choices_and_11, [], choices_orr_11, [], choices_eor_11, [], choices_ret_11⟩
def batch12 : Batch := ⟨entries12, rows12, bound12, [1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129], indices12, [], choices_and_12, [], choices_orr_12, [], choices_eor_12, [], choices_ret_12⟩
def batch13 : Batch := ⟨entries13, rows13, bound13, [1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137], indices13, [], choices_and_13, [], choices_orr_13, [], choices_eor_13, [], choices_ret_13⟩
def batch14 : Batch := ⟨entries14, rows14, bound14, [1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145], indices14, [], choices_and_14, [], choices_orr_14, [], choices_eor_14, [], choices_ret_14⟩
def batch15 : Batch := ⟨entries15, rows15, bound15, [1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153], indices15, [], choices_and_15, [], choices_orr_15, [], choices_eor_15, [], choices_ret_15⟩
def batch16 : Batch := ⟨entries16, rows16, bound16, [1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161], indices16, [], choices_and_16, [], choices_orr_16, [], choices_eor_16, [], choices_ret_16⟩
def batch17 : Batch := ⟨entries17, rows17, bound17, [1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169], indices17, [], choices_and_17, [], choices_orr_17, [], choices_eor_17, [], choices_ret_17⟩
def batch18 : Batch := ⟨entries18, rows18, bound18, [1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177], indices18, [], choices_and_18, [], choices_orr_18, [], choices_eor_18, [], choices_ret_18⟩
def batch19 : Batch := ⟨entries19, rows19, bound19, [1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185], indices19, [], choices_and_19, [], choices_orr_19, [], choices_eor_19, [], choices_ret_19⟩
def batch20 : Batch := ⟨entries20, rows20, bound20, [1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193], indices20, [], choices_and_20, [], choices_orr_20, [], choices_eor_20, [], choices_ret_20⟩
def batch21 : Batch := ⟨entries21, rows21, bound21, [1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201], indices21, [], choices_and_21, [], choices_orr_21, [], choices_eor_21, [], choices_ret_21⟩
def batch22 : Batch := ⟨entries22, rows22, bound22, [1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209], indices22, [], choices_and_22, [], choices_orr_22, [], choices_eor_22, [], choices_ret_22⟩
def batch23 : Batch := ⟨entries23, rows23, bound23, [1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217], indices23, [], choices_and_23, [], choices_orr_23, [], choices_eor_23, [], choices_ret_23⟩
def batch24 : Batch := ⟨entries24, rows24, bound24, [1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225], indices24, [], choices_and_24, [], choices_orr_24, [], choices_eor_24, [], choices_ret_24⟩
def batch25 : Batch := ⟨entries25, rows25, bound25, [1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233], indices25, [], choices_and_25, [], choices_orr_25, [], choices_eor_25, [], choices_ret_25⟩
def batch26 : Batch := ⟨entries26, rows26, bound26, [1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241], indices26, [], choices_and_26, [], choices_orr_26, [], choices_eor_26, [], choices_ret_26⟩
def batch27 : Batch := ⟨entries27, rows27, bound27, [1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249], indices27, [], choices_and_27, [], choices_orr_27, [], choices_eor_27, [], choices_ret_27⟩
def batch28 : Batch := ⟨entries28, rows28, bound28, [1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257], indices28, [], choices_and_28, [], choices_orr_28, [], choices_eor_28, [], choices_ret_28⟩
def batch29 : Batch := ⟨entries29, rows29, bound29, [1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265], indices29, [], choices_and_29, [], choices_orr_29, [], choices_eor_29, [], choices_ret_29⟩
def batch30 : Batch := ⟨entries30, rows30, bound30, [1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273], indices30, [], choices_and_30, [], choices_orr_30, [], choices_eor_30, [], choices_ret_30⟩
def batch31 : Batch := ⟨entries31, rows31, bound31, [1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281], indices31, [], choices_and_31, [], choices_orr_31, [], choices_eor_31, [], choices_ret_31⟩
def batch32 : Batch := ⟨entries32, rows32, bound32, [1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289], indices32, [], choices_and_32, [], choices_orr_32, [], choices_eor_32, [], choices_ret_32⟩
def batch33 : Batch := ⟨entries33, rows33, bound33, [1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297], indices33, [], choices_and_33, [], choices_orr_33, [], choices_eor_33, [], choices_ret_33⟩
def batch34 : Batch := ⟨entries34, rows34, bound34, [1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305], indices34, [], choices_and_34, [], choices_orr_34, [], choices_eor_34, [], choices_ret_34⟩
def batch35 : Batch := ⟨entries35, rows35, bound35, [1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313], indices35, [], choices_and_35, [], choices_orr_35, [], choices_eor_35, [], choices_ret_35⟩
def batch36 : Batch := ⟨entries36, rows36, bound36, [1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321], indices36, [], choices_and_36, [], choices_orr_36, [], choices_eor_36, [], choices_ret_36⟩
def batch37 : Batch := ⟨entries37, rows37, bound37, [1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329], indices37, [], choices_and_37, [], choices_orr_37, [], choices_eor_37, [], choices_ret_37⟩
def batch38 : Batch := ⟨entries38, rows38, bound38, [1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337], indices38, [], choices_and_38, [], choices_orr_38, [], choices_eor_38, [], choices_ret_38⟩
def batch39 : Batch := ⟨entries39, rows39, bound39, [1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345], indices39, [], choices_and_39, [], choices_orr_39, [], choices_eor_39, [], choices_ret_39⟩
def batch40 : Batch := ⟨entries40, rows40, bound40, [1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353], indices40, [], choices_and_40, [], choices_orr_40, [], choices_eor_40, [], choices_ret_40⟩
def batch41 : Batch := ⟨entries41, rows41, bound41, [1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361], indices41, [], choices_and_41, [], choices_orr_41, [], choices_eor_41, [], choices_ret_41⟩
def batch42 : Batch := ⟨entries42, rows42, bound42, [1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369], indices42, [], choices_and_42, [], choices_orr_42, [], choices_eor_42, [], choices_ret_42⟩
def batch43 : Batch := ⟨entries43, rows43, bound43, [1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377], indices43, [], choices_and_43, [], choices_orr_43, [], choices_eor_43, [], choices_ret_43⟩
def batch44 : Batch := ⟨entries44, rows44, bound44, [1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385], indices44, [], choices_and_44, [], choices_orr_44, [], choices_eor_44, [], choices_ret_44⟩
def batch45 : Batch := ⟨entries45, rows45, bound45, [1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393], indices45, [], choices_and_45, [], choices_orr_45, [], choices_eor_45, [], choices_ret_45⟩
def batch46 : Batch := ⟨entries46, rows46, bound46, [1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401], indices46, [], choices_and_46, [], choices_orr_46, [], choices_eor_46, [], choices_ret_46⟩
def batch47 : Batch := ⟨entries47, rows47, bound47, [1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409], indices47, [], choices_and_47, [], choices_orr_47, [], choices_eor_47, [], choices_ret_47⟩
def batch48 : Batch := ⟨entries48, rows48, bound48, [1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417], indices48, [], choices_and_48, [], choices_orr_48, [], choices_eor_48, [], choices_ret_48⟩
def batch49 : Batch := ⟨entries49, rows49, bound49, [1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425], indices49, [], choices_and_49, [], choices_orr_49, [], choices_eor_49, [], choices_ret_49⟩
def batch50 : Batch := ⟨entries50, rows50, bound50, [1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433], indices50, [], choices_and_50, [], choices_orr_50, [], choices_eor_50, [], choices_ret_50⟩
def batch51 : Batch := ⟨entries51, rows51, bound51, [1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441], indices51, [], choices_and_51, [], choices_orr_51, [], choices_eor_51, [], choices_ret_51⟩
def batch52 : Batch := ⟨entries52, rows52, bound52, [1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449], indices52, [], choices_and_52, [], choices_orr_52, [], choices_eor_52, [], choices_ret_52⟩
def batch53 : Batch := ⟨entries53, rows53, bound53, [1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457], indices53, [], choices_and_53, [], choices_orr_53, [], choices_eor_53, [], choices_ret_53⟩
def batch54 : Batch := ⟨entries54, rows54, bound54, [1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465], indices54, [], choices_and_54, [], choices_orr_54, [], choices_eor_54, [], choices_ret_54⟩
def batch55 : Batch := ⟨entries55, rows55, bound55, [1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473], indices55, [], choices_and_55, [], choices_orr_55, [], choices_eor_55, [], choices_ret_55⟩
def batch56 : Batch := ⟨entries56, rows56, bound56, [1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481], indices56, [], choices_and_56, [], choices_orr_56, [], choices_eor_56, [], choices_ret_56⟩
def batch57 : Batch := ⟨entries57, rows57, bound57, [1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489], indices57, [], choices_and_57, [], choices_orr_57, [], choices_eor_57, [], choices_ret_57⟩
def batch58 : Batch := ⟨entries58, rows58, bound58, [1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497], indices58, [], choices_and_58, [], choices_orr_58, [], choices_eor_58, [], choices_ret_58⟩
def batch59 : Batch := ⟨entries59, rows59, bound59, [1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505], indices59, [], choices_and_59, [], choices_orr_59, [], choices_eor_59, [], choices_ret_59⟩
def batch60 : Batch := ⟨entries60, rows60, bound60, [1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513], indices60, [], choices_and_60, [], choices_orr_60, [], choices_eor_60, [], choices_ret_60⟩
def batch61 : Batch := ⟨entries61, rows61, bound61, [1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521], indices61, [], choices_and_61, [], choices_orr_61, [], choices_eor_61, [], choices_ret_61⟩
def batch62 : Batch := ⟨entries62, rows62, bound62, [1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529], indices62, [], choices_and_62, [], choices_orr_62, [], choices_eor_62, [1522], choices_ret_62⟩
def batch63 : Batch := ⟨entries63, rows63, bound63, [1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537], indices63, [], choices_and_63, [], choices_orr_63, [], choices_eor_63, [], choices_ret_63⟩
def batch64 : Batch := ⟨entries64, rows64, bound64, [1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545], indices64, [], choices_and_64, [], choices_orr_64, [], choices_eor_64, [], choices_ret_64⟩
def batch65 : Batch := ⟨entries65, rows65, bound65, [1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553], indices65, [], choices_and_65, [], choices_orr_65, [], choices_eor_65, [], choices_ret_65⟩
def batch66 : Batch := ⟨entries66, rows66, bound66, [1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561], indices66, [], choices_and_66, [], choices_orr_66, [], choices_eor_66, [], choices_ret_66⟩
def batch67 : Batch := ⟨entries67, rows67, bound67, [1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569], indices67, [], choices_and_67, [], choices_orr_67, [], choices_eor_67, [], choices_ret_67⟩
def batch68 : Batch := ⟨entries68, rows68, bound68, [1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577], indices68, [], choices_and_68, [], choices_orr_68, [], choices_eor_68, [], choices_ret_68⟩
def batch69 : Batch := ⟨entries69, rows69, bound69, [1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585], indices69, [], choices_and_69, [], choices_orr_69, [], choices_eor_69, [], choices_ret_69⟩
def batch70 : Batch := ⟨entries70, rows70, bound70, [1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593], indices70, [], choices_and_70, [], choices_orr_70, [], choices_eor_70, [], choices_ret_70⟩
def batch71 : Batch := ⟨entries71, rows71, bound71, [1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601], indices71, [], choices_and_71, [], choices_orr_71, [], choices_eor_71, [], choices_ret_71⟩
def batch72 : Batch := ⟨entries72, rows72, bound72, [1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609], indices72, [], choices_and_72, [], choices_orr_72, [], choices_eor_72, [], choices_ret_72⟩
def batch73 : Batch := ⟨entries73, rows73, bound73, [1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617], indices73, [], choices_and_73, [], choices_orr_73, [], choices_eor_73, [], choices_ret_73⟩
def batch74 : Batch := ⟨entries74, rows74, bound74, [1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625], indices74, [], choices_and_74, [], choices_orr_74, [], choices_eor_74, [], choices_ret_74⟩
def batch75 : Batch := ⟨entries75, rows75, bound75, [1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633], indices75, [], choices_and_75, [], choices_orr_75, [], choices_eor_75, [], choices_ret_75⟩
def batch76 : Batch := ⟨entries76, rows76, bound76, [1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641], indices76, [], choices_and_76, [], choices_orr_76, [], choices_eor_76, [], choices_ret_76⟩
def batch77 : Batch := ⟨entries77, rows77, bound77, [1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649], indices77, [], choices_and_77, [], choices_orr_77, [], choices_eor_77, [], choices_ret_77⟩
def batch78 : Batch := ⟨entries78, rows78, bound78, [1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657], indices78, [], choices_and_78, [], choices_orr_78, [], choices_eor_78, [], choices_ret_78⟩
def batch79 : Batch := ⟨entries79, rows79, bound79, [1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665], indices79, [], choices_and_79, [], choices_orr_79, [], choices_eor_79, [], choices_ret_79⟩
def batch80 : Batch := ⟨entries80, rows80, bound80, [1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673], indices80, [], choices_and_80, [], choices_orr_80, [], choices_eor_80, [], choices_ret_80⟩
def batch81 : Batch := ⟨entries81, rows81, bound81, [1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681], indices81, [], choices_and_81, [], choices_orr_81, [], choices_eor_81, [], choices_ret_81⟩
def batch82 : Batch := ⟨entries82, rows82, bound82, [1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689], indices82, [], choices_and_82, [], choices_orr_82, [], choices_eor_82, [], choices_ret_82⟩
def batch83 : Batch := ⟨entries83, rows83, bound83, [1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697], indices83, [], choices_and_83, [], choices_orr_83, [], choices_eor_83, [], choices_ret_83⟩
def batch84 : Batch := ⟨entries84, rows84, bound84, [1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705], indices84, [], choices_and_84, [], choices_orr_84, [], choices_eor_84, [], choices_ret_84⟩
def batch85 : Batch := ⟨entries85, rows85, bound85, [1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713], indices85, [], choices_and_85, [], choices_orr_85, [], choices_eor_85, [], choices_ret_85⟩
def batch86 : Batch := ⟨entries86, rows86, bound86, [1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721], indices86, [], choices_and_86, [], choices_orr_86, [], choices_eor_86, [], choices_ret_86⟩
def batch87 : Batch := ⟨entries87, rows87, bound87, [1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729], indices87, [], choices_and_87, [], choices_orr_87, [], choices_eor_87, [], choices_ret_87⟩
def batch88 : Batch := ⟨entries88, rows88, bound88, [1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737], indices88, [], choices_and_88, [], choices_orr_88, [], choices_eor_88, [], choices_ret_88⟩
def batch89 : Batch := ⟨entries89, rows89, bound89, [1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745], indices89, [], choices_and_89, [], choices_orr_89, [], choices_eor_89, [], choices_ret_89⟩
def batch90 : Batch := ⟨entries90, rows90, bound90, [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753], indices90, [], choices_and_90, [], choices_orr_90, [], choices_eor_90, [], choices_ret_90⟩
def batch91 : Batch := ⟨entries91, rows91, bound91, [1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761], indices91, [], choices_and_91, [], choices_orr_91, [], choices_eor_91, [], choices_ret_91⟩
def batch92 : Batch := ⟨entries92, rows92, bound92, [1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769], indices92, [], choices_and_92, [], choices_orr_92, [], choices_eor_92, [], choices_ret_92⟩
def batch93 : Batch := ⟨entries93, rows93, bound93, [1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777], indices93, [], choices_and_93, [], choices_orr_93, [], choices_eor_93, [], choices_ret_93⟩
def batch94 : Batch := ⟨entries94, rows94, bound94, [1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785], indices94, [], choices_and_94, [], choices_orr_94, [], choices_eor_94, [], choices_ret_94⟩
def batch95 : Batch := ⟨entries95, rows95, bound95, [1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793], indices95, [], choices_and_95, [], choices_orr_95, [1788], choices_eor_95, [], choices_ret_95⟩
def batch96 : Batch := ⟨entries96, rows96, bound96, [1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801], indices96, [], choices_and_96, [], choices_orr_96, [], choices_eor_96, [], choices_ret_96⟩
def batch97 : Batch := ⟨entries97, rows97, bound97, [1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809], indices97, [], choices_and_97, [], choices_orr_97, [], choices_eor_97, [], choices_ret_97⟩
def batch98 : Batch := ⟨entries98, rows98, bound98, [1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817], indices98, [], choices_and_98, [], choices_orr_98, [], choices_eor_98, [], choices_ret_98⟩
def batch99 : Batch := ⟨entries99, rows99, bound99, [1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825], indices99, [], choices_and_99, [], choices_orr_99, [], choices_eor_99, [], choices_ret_99⟩
def batch100 : Batch := ⟨entries100, rows100, bound100, [1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833], indices100, [], choices_and_100, [], choices_orr_100, [], choices_eor_100, [], choices_ret_100⟩
def batch101 : Batch := ⟨entries101, rows101, bound101, [1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841], indices101, [], choices_and_101, [], choices_orr_101, [], choices_eor_101, [], choices_ret_101⟩
def batch102 : Batch := ⟨entries102, rows102, bound102, [1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849], indices102, [1845], choices_and_102, [], choices_orr_102, [], choices_eor_102, [], choices_ret_102⟩
def batch103 : Batch := ⟨entries103, rows103, bound103, [1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857], indices103, [], choices_and_103, [], choices_orr_103, [], choices_eor_103, [], choices_ret_103⟩
def batch104 : Batch := ⟨entries104, rows104, bound104, [1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865], indices104, [], choices_and_104, [1858], choices_orr_104, [], choices_eor_104, [], choices_ret_104⟩
def batch105 : Batch := ⟨entries105, rows105, bound105, [1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873], indices105, [], choices_and_105, [], choices_orr_105, [], choices_eor_105, [], choices_ret_105⟩
def batch106 : Batch := ⟨entries106, rows106, bound106, [1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881], indices106, [], choices_and_106, [], choices_orr_106, [], choices_eor_106, [], choices_ret_106⟩
def batch107 : Batch := ⟨entries107, rows107, bound107, [1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889], indices107, [], choices_and_107, [], choices_orr_107, [], choices_eor_107, [], choices_ret_107⟩
def batch108 : Batch := ⟨entries108, rows108, bound108, [1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897], indices108, [], choices_and_108, [], choices_orr_108, [], choices_eor_108, [], choices_ret_108⟩
def batch109 : Batch := ⟨entries109, rows109, bound109, [1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905], indices109, [], choices_and_109, [], choices_orr_109, [], choices_eor_109, [], choices_ret_109⟩
def batch110 : Batch := ⟨entries110, rows110, bound110, [1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913], indices110, [], choices_and_110, [], choices_orr_110, [], choices_eor_110, [], choices_ret_110⟩
def batch111 : Batch := ⟨entries111, rows111, bound111, [1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921], indices111, [], choices_and_111, [], choices_orr_111, [], choices_eor_111, [], choices_ret_111⟩
def batch112 : Batch := ⟨entries112, rows112, bound112, [1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929], indices112, [], choices_and_112, [], choices_orr_112, [], choices_eor_112, [], choices_ret_112⟩
def batch113 : Batch := ⟨entries113, rows113, bound113, [1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937], indices113, [], choices_and_113, [], choices_orr_113, [], choices_eor_113, [], choices_ret_113⟩
def batch114 : Batch := ⟨entries114, rows114, bound114, [1938, 1939, 1940, 1941, 1942], indices114, [], choices_and_114, [], choices_orr_114, [], choices_eor_114, [], choices_ret_114⟩

def batches : List Batch := [batch0, batch1, batch2, batch3, batch4, batch5, batch6, batch7, batch8, batch9, batch10, batch11, batch12, batch13, batch14, batch15, batch16, batch17, batch18, batch19, batch20, batch21, batch22, batch23, batch24, batch25, batch26, batch27, batch28, batch29, batch30, batch31, batch32, batch33, batch34, batch35, batch36, batch37, batch38, batch39, batch40, batch41, batch42, batch43, batch44, batch45, batch46, batch47, batch48, batch49, batch50, batch51, batch52, batch53, batch54, batch55, batch56, batch57, batch58, batch59, batch60, batch61, batch62, batch63, batch64, batch65, batch66, batch67, batch68, batch69, batch70, batch71, batch72, batch73, batch74, batch75, batch76, batch77, batch78, batch79, batch80, batch81, batch82, batch83, batch84, batch85, batch86, batch87, batch88, batch89, batch90, batch91, batch92, batch93, batch94, batch95, batch96, batch97, batch98, batch99, batch100, batch101, batch102, batch103, batch104, batch105, batch106, batch107, batch108, batch109, batch110, batch111, batch112, batch113, batch114]
def embedded : List CheckedRow := batches.flatMap Batch.entries
def table : List Row := batches.flatMap Batch.rows

theorem table_bound : embedded.map CheckedRow.row = table := by
  rw [embedded, table, List.map_flatMap]
  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.bound)

theorem table_index_batches : table.map Row.index = batches.flatMap Batch.indexList := by
  rw [table, List.map_flatMap]
  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.indices_bound)

theorem table_indices : table.map Row.index = [1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081, 1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175, 1176, 1177, 1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193, 1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201, 1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209, 1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225, 1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257, 1258, 1259, 1260, 1261, 1262, 1263, 1264, 1265, 1266, 1267, 1268, 1269, 1270, 1271, 1272, 1273, 1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281, 1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289, 1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313, 1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409, 1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420, 1421, 1422, 1423, 1424, 1425, 1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433, 1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441, 1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449, 1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457, 1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465, 1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473, 1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481, 1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489, 1490, 1491, 1492, 1493, 1494, 1495, 1496, 1497, 1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529, 1530, 1531, 1532, 1533, 1534, 1535, 1536, 1537, 1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545, 1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553, 1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561, 1562, 1563, 1564, 1565, 1566, 1567, 1568, 1569, 1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625, 1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633, 1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641, 1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649, 1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659, 1660, 1661, 1662, 1663, 1664, 1665, 1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673, 1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681, 1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689, 1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705, 1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713, 1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729, 1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737, 1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745, 1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753, 1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761, 1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769, 1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777, 1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793, 1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801, 1802, 1803, 1804, 1805, 1806, 1807, 1808, 1809, 1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817, 1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825, 1826, 1827, 1828, 1829, 1830, 1831, 1832, 1833, 1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841, 1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849, 1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857, 1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865, 1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873, 1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881, 1882, 1883, 1884, 1885, 1886, 1887, 1888, 1889, 1890, 1891, 1892, 1893, 1894, 1895, 1896, 1897, 1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905, 1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913, 1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921, 1922, 1923, 1924, 1925, 1926, 1927, 1928, 1929, 1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937, 1938, 1939, 1940, 1941, 1942] := by
  rw [table_index_batches]; rfl

theorem table_choices (word : Word) : choices table word.bits (-1) = batches.flatMap (fun b => b.matches word) := by
  rw [table, choices_flatMap]
  exact congrArg (fun f => batches.flatMap f) (funext fun b => b.proved word)

theorem embedded_bytes_bound (a : CheckedRow) (_ : a ∈ embedded) :
    a.clause.valid = true ∧ String.join a.clause.chunks = String.join a.raw ∧ a.clause.row = a.row := row_bound a

theorem unique_and : choices table 167837696#32 (-1) = [1845] := by
  change choices table Word.and.bits (-1) = _
  rw [table_choices]; rfl
theorem first_and : first table 167837696#32 (-1) = some 1845 := by
  rw [first, unique_and]; rfl

theorem unique_orr : choices table 704708608#32 (-1) = [1858] := by
  change choices table Word.orr.bits (-1) = _
  rw [table_choices]; rfl
theorem first_orr : first table 704708608#32 (-1) = some 1858 := by
  rw [first, unique_orr]; rfl

theorem unique_eor : choices table 1241579520#32 (-1) = [1788] := by
  change choices table Word.eor.bits (-1) = _
  rw [table_choices]; rfl
theorem first_eor : first table 1241579520#32 (-1) = some 1788 := by
  rw [first, unique_eor]; rfl

theorem unique_ret : choices table 3596551104#32 (-1) = [1522] := by
  change choices table Word.ret.bits (-1) = _
  rw [table_choices]; rfl
theorem first_ret : first table 3596551104#32 (-1) = some 1522 := by
  rw [first, unique_ret]; rfl

end Oak.ArmDecoderClassification
