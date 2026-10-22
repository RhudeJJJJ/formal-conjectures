/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4998 : Family 10 := level10.get ⟨1618,by decide⟩
def sourceMap4998 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4998 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4998_checked : acceptsGraphIso
    (source (graph core4998) (root 10) 2 2) DegreeTwoThreeSpectrum7599.graph sourceMap4998=true := by decide +kernel
theorem fusedMap4998_checked : acceptsGraphIso
    (fused (graph core4998) (root 10) 2 2) DegreeTwoThreeSpectrum6173.graph fusedMap4998=true := by decide +kernel
theorem certified4998 : Certified (graph core4998) (root 10) 2 2 :=
  of_native_maps core4998 DegreeTwoThreeSpectrum7599.graph DegreeTwoThreeSpectrum6173.graph
    sourceMap4998 fusedMap4998 sourceMap4998_checked fusedMap4998_checked
    DegreeTwoThreeFiniteComparisons.comparison4998
#print axioms sourceMap4998_checked
#print axioms fusedMap4998_checked
#print axioms certified4998
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
