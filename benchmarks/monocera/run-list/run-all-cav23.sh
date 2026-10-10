#!/bin/bash

TWALL=$1  #wall time out #Paper value:300
TCPU=$2   #cpu time out Paper value:2700
NRTESTS=$3    #number of tests per category, 0 for all tests
ALLORSINGLEPROVER=$4  #either "all" or some specific tool 
SEED=$5   #seed for shuffling tests

get_fixed_random()
{
    openssl enc -aes-256-ctr -pass pass:"$1" -nosalt </dev/zero 2>/dev/null
}

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" &>/dev/null && pwd -P)



FILEPATH=${script_dir}/..

TESTS_FOLDER=polished_tests

# Edit below two lines to change what to test
# Available provers: monocera tricera seahorn cpa
# Available ops: forall sum min max
if [[ "$ALLORSINGLEPROVER" == "all" ]]
then
	PROVERS="seahorn monocera tricera cpa"
else
	PROVERS=$ALLORSINGLEPROVER
fi
OPS="sum min max forall"
NO_MALLOC=0

# send stdout and stderr output to the log
SCRIPT_NAME=`basename "$0"`
LOG_FILE="${SCRIPT_NAME}_$(date '+%Y-%m-%d-%H:%M:%S').log"

exec 3>&1 1>>${LOG_FILE} 2>&1

printf "Output log for this script can also be found at\n$LOG_FILE \n\n" 1>&3

if [ $( docker ps -a -f name=seahorncont | wc -l ) -eq 2 ]; then
  docker stop seahorncont
  docker rm seahorncont
fi >/dev/null

docker run  -v $FILEPATH:/host --name seahorncont -dit seahorn/seahorn-llvm10:nightly >/dev/null

echo "Running tests with Wall/CPU imeout: ${TWALL}/${TCPU} s." | tee /dev/fd/3
printf '  For each tool in: {%s}\n' "${PROVERS[@]}"  | tee /dev/fd/3
printf '  For each operator in {%s}\n' "${OPS[@]}"  | tee /dev/fd/3
if [ "$NRTESTS" -gt "0" ]
then
    printf '  Limiting test cases to %s per operator and tool\n' "$NRTESTS"  | tee /dev/fd/3
    printf '  Using the seed %s for the random selection of benchmarks.' "$4"   | tee /dev/fd/3
fi

for prover in $PROVERS
do
  for op in $OPS
  do
    date=$(date '+%Y-%m-%d %H:%M:%S')
    printf "\n  - $prover/$op (started $date)"  | tee /dev/fd/3
    mkdir -p $FILEPATH/run-test-result/${prover}/${op}
    cd $FILEPATH/run-test-result/${prover}
    list_fname=${op}_list
    if (($NO_MALLOC==1))
    then
      list_fname+="_nomalloc"
      nomalloc="_nomalloc"
    else
      nomalloc=""
    fi
    filelist=$(find $FILEPATH/${TESTS_FOLDER}${nomalloc}/${prover}/${op}/*.c -type f | xargs  realpath)
    if [ "$NRTESTS" -gt "0" ]
    then
    	testsToTake=$NRTESTS
    	filelist=$((shuf --random-source=<(get_fixed_random $4) | head -n $NRTESTS) <<< $filelist)
    fi
    if [[ "$prover" == "seahorn" ]]
    then
	#/host/polished_tests/seahorn/max/max_leq-10.c
	#/home/cav23/artifact-168/run_tests/polished_tests/monocera/max/max_leq-100.c
     	cat <<< "$filelist" > "$FILEPATH/run-test-result/${prover}/${op}/${list_fname}"
     	sed -i 's/home\/cav23\/artifact-168\/run_tests/host/g' "$FILEPATH/run-test-result/${prover}/${op}/${list_fname}"
      	filelistpath=${prover}/${op}/${list_fname}
      	cmd1="/host/run-list/run-sea-cav23.sh $prover $op $TWALL $TCPU $filelistpath $nomalloc"
      	docker exec seahorncont $cmd1
    else
    	cat <<< "$filelist" > "$FILEPATH/run-test-result/${prover}/${op}/${list_fname}"
      #find $FILEPATH/${TESTS_FOLDER}${nomalloc}/${prover}/${op}/*.c -type f | sort | xargs  realpath  > $FILEPATH/run-test-result/${prover}/${op}/${list_fname}
      $FILEPATH/run-list/run-list-${prover}-cav23 $FILEPATH/run-test-result/${prover}/${op}/${list_fname} -twall $TWALL -tcpu $TCPU
    fi | tee /dev/fd/3 
  done
done

docker stop seahorncont
docker rm seahorncont

