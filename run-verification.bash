#!/bin/sh
stack exec -- liquid src/RGRef.hs src/MonotonicCounter.hs src/LockfreeMonotonicCounter.hs src/MonotonicCounterClient.hs src/CASList.hs src/HellerSet.hs
