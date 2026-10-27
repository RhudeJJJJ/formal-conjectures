/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4176 : Family 8 := level8.get ⟨225,by decide⟩
def sourceMap4176 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,11,12,13,14,5,6,7,8,9,10] (sourceLabel 8 2 2 v)
def fusedMap4176 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4176_checked : acceptsGraphIso
    (source (graph core4176) (root 8) 2 2) DegreeTwoThreeSpectrum3816.graph sourceMap4176=true := by decide +kernel
theorem fusedMap4176_checked : acceptsGraphIso
    (fused (graph core4176) (root 8) 2 2) DegreeTwoThreeSpectrum2566.graph fusedMap4176=true := by decide +kernel
theorem certified4176 : Certified (graph core4176) (root 8) 2 2 :=
  of_native_maps core4176 DegreeTwoThreeSpectrum3816.graph DegreeTwoThreeSpectrum2566.graph
    sourceMap4176 fusedMap4176 sourceMap4176_checked fusedMap4176_checked
    DegreeTwoThreeFiniteComparisons.comparison4176
#print axioms sourceMap4176_checked
#print axioms fusedMap4176_checked
#print axioms certified4176
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
