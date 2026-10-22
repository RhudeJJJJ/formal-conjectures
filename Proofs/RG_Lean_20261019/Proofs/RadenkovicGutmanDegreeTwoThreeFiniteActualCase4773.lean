/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4773 : Family 10 := level10.get ⟨1062,by decide⟩
def sourceMap4773 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4773 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4773_checked : acceptsGraphIso
    (source (graph core4773) (root 10) 2 2) DegreeTwoThreeSpectrum7140.graph sourceMap4773=true := by decide +kernel
theorem fusedMap4773_checked : acceptsGraphIso
    (fused (graph core4773) (root 10) 2 2) DegreeTwoThreeSpectrum6109.graph fusedMap4773=true := by decide +kernel
theorem certified4773 : Certified (graph core4773) (root 10) 2 2 :=
  of_native_maps core4773 DegreeTwoThreeSpectrum7140.graph DegreeTwoThreeSpectrum6109.graph
    sourceMap4773 fusedMap4773 sourceMap4773_checked fusedMap4773_checked
    DegreeTwoThreeFiniteComparisons.comparison4773
#print axioms sourceMap4773_checked
#print axioms fusedMap4773_checked
#print axioms certified4773
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
