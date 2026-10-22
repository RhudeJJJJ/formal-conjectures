/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4957 : Family 10 := level10.get ⟨1504,by decide⟩
def sourceMap4957 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4957 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4957_checked : acceptsGraphIso
    (source (graph core4957) (root 10) 2 2) DegreeTwoThreeSpectrum7387.graph sourceMap4957=true := by decide +kernel
theorem fusedMap4957_checked : acceptsGraphIso
    (fused (graph core4957) (root 10) 2 2) DegreeTwoThreeSpectrum7011.graph fusedMap4957=true := by decide +kernel
theorem certified4957 : Certified (graph core4957) (root 10) 2 2 :=
  of_native_maps core4957 DegreeTwoThreeSpectrum7387.graph DegreeTwoThreeSpectrum7011.graph
    sourceMap4957 fusedMap4957 sourceMap4957_checked fusedMap4957_checked
    DegreeTwoThreeFiniteComparisons.comparison4957
#print axioms sourceMap4957_checked
#print axioms fusedMap4957_checked
#print axioms certified4957
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
