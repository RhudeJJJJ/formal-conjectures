/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4829 : Family 10 := level10.get ⟨1201,by decide⟩
def sourceMap4829 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4829 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4829_checked : acceptsGraphIso
    (source (graph core4829) (root 10) 2 2) DegreeTwoThreeSpectrum7288.graph sourceMap4829=true := by decide +kernel
theorem fusedMap4829_checked : acceptsGraphIso
    (fused (graph core4829) (root 10) 2 2) DegreeTwoThreeSpectrum6379.graph fusedMap4829=true := by decide +kernel
theorem certified4829 : Certified (graph core4829) (root 10) 2 2 :=
  of_native_maps core4829 DegreeTwoThreeSpectrum7288.graph DegreeTwoThreeSpectrum6379.graph
    sourceMap4829 fusedMap4829 sourceMap4829_checked fusedMap4829_checked
    DegreeTwoThreeFiniteComparisons.comparison4829
#print axioms sourceMap4829_checked
#print axioms fusedMap4829_checked
#print axioms certified4829
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
