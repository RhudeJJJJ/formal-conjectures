/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4973 : Family 10 := level10.get ⟨1555,by decide⟩
def sourceMap4973 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4973 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4973_checked : acceptsGraphIso
    (source (graph core4973) (root 10) 2 2) DegreeTwoThreeSpectrum7574.graph sourceMap4973=true := by decide +kernel
theorem fusedMap4973_checked : acceptsGraphIso
    (fused (graph core4973) (root 10) 2 2) DegreeTwoThreeSpectrum6011.graph fusedMap4973=true := by decide +kernel
theorem certified4973 : Certified (graph core4973) (root 10) 2 2 :=
  of_native_maps core4973 DegreeTwoThreeSpectrum7574.graph DegreeTwoThreeSpectrum6011.graph
    sourceMap4973 fusedMap4973 sourceMap4973_checked fusedMap4973_checked
    DegreeTwoThreeFiniteComparisons.comparison4973
#print axioms sourceMap4973_checked
#print axioms fusedMap4973_checked
#print axioms certified4973
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
