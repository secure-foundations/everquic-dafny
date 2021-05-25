import subprocess, os, sys
import time
from optparse import OptionParser

conf_string = """address:"%s"
port:"4321"
in_path:"%s"
loss:"%d"
"""
conf_path = "../data/temp.conf"

KB = 1024 
lo_ip = "127.0.0.1"
lan_server_ip = "[redacted ip]"
ssh_command = "ssh %s " % lan_server_ip

def gen_data(n_kb):
    file_path = "../data/%dK.bin" % n_kb 
    if not os.path.isfile(file_path):
        os.system("head -c %dK </dev/urandom > %s" % (n_kb, file_path))
    assert (os.stat(file_path).st_size == n_kb * KB)
    return file_path

def gen_config(data_file_path, loss_rate, server_ip):
    filled_conf = conf_string % (server_ip, data_file_path, loss_rate)
    with open(conf_path, "w") as f:
        f.write(filled_conf)

def do_setup(n_kb, loss_rate, server_ip):
    data_file_path = gen_data(n_kb)
    gen_config(data_file_path, loss_rate, server_ip)
    return data_file_path

def do_test(n_kb, loss_rate, data_file_path):
    print("lo test %dK" % n_kb)

    server_command = "./server " + conf_path
    client_command = "./client " + conf_path
    FNULL = open(os.devnull, 'w')

    server = subprocess.Popen(server_command, stdout=FNULL, stderr=FNULL, cwd="../obj", shell=True, env={"LD_LIBRARY_PATH":"../mipki"})
    start = time.time()
    client = subprocess.Popen(client_command, stdout=FNULL, stderr=FNULL, cwd="../obj", shell=True, env={"LD_LIBRARY_PATH":"../mipki"})
    client.wait()
    elapsed = (time.time() - start)
    subprocess.check_output(["killall", "server"])
    server.wait()

    subprocess.check_output(["diff", "../obj/result.bin", data_file_path])
    os.system("rm ../obj/result.bin")
    FNULL.close()

    throughput = (n_kb / elapsed / 1024)
    result = "%d,%d,%f,%f\n" % (n_kb * 1024, loss_rate, elapsed, throughput)
    print(result.strip())
    return result

def do_lan_test(n_kb, loss_rate, data_file_path):
    print("lan test %dK" % n_kb)

    data_file_name = "%dK.bin" % n_kb
    # sync config file first
    os.system("scp %s %s:quic-dafny/data >/dev/null" % (conf_path, lan_server_ip))
    scp_temp_name = "scp.bin"

    server_command = ssh_command + "\"cd quic-dafny/obj && LD_LIBRARY_PATH=../mipki ./server %s\"" % conf_path
    client_command = "./client " + conf_path
    FNULL = open(os.devnull, 'w')

    server = subprocess.Popen(server_command, stdout=FNULL, stderr=FNULL, shell=True)
    time.sleep(1)  # wait for the server to init, then start the test
    # use scp to transfer the file first, so that we can compare the output
    os.system("scp %s:quic-dafny/data/%s %s > /dev/null" % (lan_server_ip, data_file_name, scp_temp_name))
    
    start = time.time()

    client = subprocess.Popen(client_command, stdout=FNULL, stderr=FNULL, cwd="../obj", shell=True, env={"LD_LIBRARY_PATH":"../mipki"})
    client.wait()

    elapsed = (time.time() - start)
    
    os.system(ssh_command + "\"killall server\"")
    server.kill()

    subprocess.check_output(["diff", "../obj/result.bin", scp_temp_name])
    os.system("rm ../obj/result.bin")
    os.system("rm " + scp_temp_name)
    FNULL.close()

    throughput = (n_kb / elapsed / 1024)
    result = "%d,%d,%f,%f\n" % (n_kb * 1024, loss_rate, elapsed, throughput)
    print(result.strip())
    return result

def do_reference_test(n_kb, loss_rate, data_file_path):
    data_file_name = "%dK.bin" % n_kb
    print("lo reference test %dK" % n_kb)

    server_command = "../ngtcp2/ngtcp2_server -q -d ../data localhost 1234 ../data/server-ecdsa.key ../data/server-ecdsa.crt"
    client_command = "../ngtcp2/ngtcp2_client -q --download=./ --timeout=1 127.0.0.1 1234 https://localhost/" + data_file_name
    FNULL = open(os.devnull, 'w')

    server = subprocess.Popen(server_command, stdout=FNULL, stderr=FNULL, shell=True)

    start = time.time()
    client = subprocess.Popen(client_command, stdout=FNULL, stderr=FNULL, shell=True)
    client.wait()
    elapsed = (time.time() - start)

    server.kill()

    subprocess.check_output(["diff", data_file_name, data_file_path])
    os.system("rm " + data_file_name)
    FNULL.close()

    throughput = (n_kb / elapsed / 1024)
    result = "%d,%d,%f,%f\n" % (n_kb * 1024, loss_rate, elapsed, throughput)
    print(result.strip())
    return result

def do_lan_reference_test(n_kb, loss_rate, data_file_path):
    data_file_name = "%dK.bin" % n_kb
    print("lan reference test %dK" % n_kb)

    scp_temp_name = "scp.bin"

    server_command = ssh_command + \
        "\"cd quic-dafny/script && ../ngtcp2/ngtcp2_server -q -d ../data %s 1234 ../data/server-ecdsa.key ../data/server-ecdsa.crt\"" % (lan_server_ip)
    client_command = "../ngtcp2/ngtcp2_client -q --download=./ --timeout=1 %s 1234 https://%s/%s" % (lan_server_ip, lan_server_ip, data_file_name)
    FNULL = open(os.devnull, 'w')

    server = subprocess.Popen(server_command, stdout=FNULL, stderr=FNULL, shell=True)
    # time.sleep(1)  # wait for the server to init, then start the test
    # use scp to transfer the file first, so that we can compare the output
    os.system("scp %s:quic-dafny/data/%s %s > /dev/null" % (lan_server_ip, data_file_name, scp_temp_name))
    
    start = time.time()
    client = subprocess.Popen(client_command, stdout=FNULL, stderr=FNULL, shell=True)
    client.wait()
    elapsed = (time.time() - start)

    os.system(ssh_command + "\"killall ngtcp2_server\"")
    server.kill()

    subprocess.check_output(["diff", data_file_name, scp_temp_name])
    os.system("rm " + data_file_name)
    os.system("rm " + scp_temp_name)
    FNULL.close()

    throughput = (n_kb / elapsed / 1024)
    result = "%d,%d,%f,%f\n" % (n_kb * 1024, loss_rate, elapsed, throughput)
    print(result.strip())
    return result

def gen_throughput_report(report_file_path, test_fun, loss_rate, repeat, sizes, server_ip):
    report = "file_size,drop_rate,elapsed_time,throughput_MBPS\n"
    print(report.strip())
    file_size = 512

    for _ in range(0, sizes):
        for _ in range(repeat):
            data_file_path = do_setup(file_size, loss_rate, server_ip)
            report += test_fun(file_size, loss_rate, data_file_path)
        file_size *= 2

    with open(report_file_path, "w") as f:
        f.write(report)

if __name__ == "__main__":
    parser = OptionParser()
    parser.add_option("-c", "--conn-mode", dest="conn_mode", default="lo", help="connection mode: lo (loop back), lan (local area network)")
    parser.add_option("-m", "--test-mode", dest="test_mode", default="t", help="test mode: t (throughput), d (drop), r (reference)")

    parser.add_option("-d", "--drop-rate", type=int, dest="drop_rate", default=0, help="set drop rate of udp")
    parser.add_option("-s", "--size", type=int, dest="file_size", default=4, help="set file size in KB")
    parser.add_option("-r", "--repeat", type=int, dest="repeat", default=1, help="number of times to repeat measurement")
    parser.add_option("-n", "--num_sizes", type=int, dest="num_sizes", default=13, help="number of sizes for csv")

    (options, args) = parser.parse_args()

    conn_mode = options.conn_mode
    test_mode = options.test_mode
    loss_rate = options.drop_rate

    if conn_mode == "lo":
        print("running test on loop back")
        if test_mode == "t":
            print("running throughput test")
            gen_throughput_report("throughput_report.csv", do_test, loss_rate, options.repeat, options.num_sizes, lo_ip)
        elif test_mode == "r":
            print("running reference test")
            gen_throughput_report("reference_throughput_report.csv", do_reference_test, loss_rate, options.repeat, options.num_sizes, lo_ip)
    elif conn_mode == "lan":
        print("running test on lan")
        if test_mode == "t":
            print("running throughput test")
            gen_throughput_report("lan_throughput_report.csv", do_lan_test, loss_rate, options.repeat, options.num_sizes, lan_server_ip)
        elif test_mode == "r":
            print("running reference test")
            gen_throughput_report("reference_lan_throughput_report.csv", do_lan_reference_test, loss_rate, options.repeat, options.num_sizes, lan_server_ip)
