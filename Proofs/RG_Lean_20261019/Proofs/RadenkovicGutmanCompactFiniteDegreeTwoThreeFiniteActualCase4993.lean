/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4993 : Family 10 := level10.get ⟨1600,by decide⟩
def sourceMap4993 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4993 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4993_checked : acceptsGraphIso
    (source (graph core4993) (root 10) 2 2) DegreeTwoThreeSpectrum7594.graph sourceMap4993=true := by decide +kernel
theorem fusedMap4993_checked : acceptsGraphIso
    (fused (graph core4993) (root 10) 2 2) DegreeTwoThreeSpectrum6115.graph fusedMap4993=true := by decide +kernel
theorem certified4993 : Certified (graph core4993) (root 10) 2 2 :=
  of_native_maps core4993 DegreeTwoThreeSpectrum7594.graph DegreeTwoThreeSpectrum6115.graph
    sourceMap4993 fusedMap4993 sourceMap4993_checked fusedMap4993_checked
    DegreeTwoThreeFiniteComparisons.comparison4993
#print axioms sourceMap4993_checked
#print axioms fusedMap4993_checked
#print axioms certified4993
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
