/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4608 : Family 10 := level10.get ⟨627,by decide⟩
def sourceMap4608 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4608 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4608_checked : acceptsGraphIso
    (source (graph core4608) (root 10) 2 2) DegreeTwoThreeSpectrum7286.graph sourceMap4608=true := by decide +kernel
theorem fusedMap4608_checked : acceptsGraphIso
    (fused (graph core4608) (root 10) 2 2) DegreeTwoThreeSpectrum5317.graph fusedMap4608=true := by decide +kernel
theorem certified4608 : Certified (graph core4608) (root 10) 2 2 :=
  of_native_maps core4608 DegreeTwoThreeSpectrum7286.graph DegreeTwoThreeSpectrum5317.graph
    sourceMap4608 fusedMap4608 sourceMap4608_checked fusedMap4608_checked
    DegreeTwoThreeFiniteComparisons.comparison4608
#print axioms sourceMap4608_checked
#print axioms fusedMap4608_checked
#print axioms certified4608
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
