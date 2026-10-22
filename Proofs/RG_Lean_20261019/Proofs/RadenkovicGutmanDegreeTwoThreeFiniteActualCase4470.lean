/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4470 : Family 10 := level10.get ⟨180,by decide⟩
def sourceMap4470 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,12,13,14,15,16,10,11,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap4470 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4470_checked : acceptsGraphIso
    (source (graph core4470) (root 10) 2 2) DegreeTwoThreeSpectrum6824.graph sourceMap4470=true := by decide +kernel
theorem fusedMap4470_checked : acceptsGraphIso
    (fused (graph core4470) (root 10) 2 2) DegreeTwoThreeSpectrum5127.graph fusedMap4470=true := by decide +kernel
theorem certified4470 : Certified (graph core4470) (root 10) 2 2 :=
  of_native_maps core4470 DegreeTwoThreeSpectrum6824.graph DegreeTwoThreeSpectrum5127.graph
    sourceMap4470 fusedMap4470 sourceMap4470_checked fusedMap4470_checked
    DegreeTwoThreeFiniteComparisons.comparison4470
#print axioms sourceMap4470_checked
#print axioms fusedMap4470_checked
#print axioms certified4470
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
