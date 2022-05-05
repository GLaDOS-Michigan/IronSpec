import numpy as np

nodes_list=['002', '003', '004', '007', '008', '009', '013', '017', '018', '023', '024', '031', '032', '035', '036', '038', '039', '053', '056', '064', '070', '087', '093', '094', '095']
hole_list=['60','61','62','63','64','65','72','73','74','75','76','77','84','85','86','87','88','89','122','137','138','139','140','141','142','143','147','157','194','217','235','236','237','238','239','240','241','247','257','283']
tasks = []
for i in np.arange(len(nodes_list)):
    tasks.append([])
for i in np.arange(len(hole_list)):
    node_id=i % 25
    # print(i, node_id, nodes_list[node_id], hole_list[i])
    tasks[node_id].append(hole_list[i])
for i in np.arange(len(nodes_list)):
    # print(i, tasks[i])
    cmd = '/proj/vm-vm-PG0/BASE-DIRECTORY/dafny-holeEval/run_hole_finder.sh '
    for t in tasks[i]:
        cmd += t + ' '
    cmd += '& disown -a'
    print(f'ssh arminvak@clnode{nodes_list[i]}.clemson.cloudlab.us \"{cmd}\" &')
#for id in 003 004 007 008 009 013 017 018 023 024 031 032 035 036 038 039 053 056 064 070 087 093 094 095;
#do
#    ssh arminvak@clnode${id}.clemson.cloudlab.us "sleep 60 & disown -a"
#done