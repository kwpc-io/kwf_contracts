#!/bin/bash
echo "#!/bin/bash
BAR1=1" | tee foo.sh
chmod u+x foo.sh 
. foo.sh
