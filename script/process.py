import sys

def process_throughput(file_name):
    rows = dict()
    with open(file_name) as f:
        for count, line in enumerate(f):
            if count == 0:
                continue
            line = line.strip().split(",")
            file_size = int(line[0])
            throughput = float(line[-1])
            if file_size not in rows:
                rows[file_size] = {"min": 4096, "max": 0, "sum": 0, "count": 0}
            row = rows[file_size]
            row["min"] = min(row["min"], throughput)
            row["max"] = max(row["max"], throughput)
            row["sum"] = row["sum"] + throughput
            row["count"] = row["count"] + 1

    with open("processed_" + file_name, "w") as f:
        f.write("file_size,min,max,medium\n")
        for file_size in sorted(rows):
            row = rows[file_size]
            medium = row["sum"] / row["count"]
            line = "%d,%f,%f,%f\n" % (file_size, row["min"], row["max"], medium) 
            f.write(line)

process_throughput(sys.argv[1])
