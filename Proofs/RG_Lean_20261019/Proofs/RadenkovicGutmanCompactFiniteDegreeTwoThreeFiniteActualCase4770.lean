/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4770 : Family 10 := level10.get ⟨1058,by decide⟩
def sourceMap4770 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4770 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4770_checked : acceptsGraphIso
    (source (graph core4770) (root 10) 2 2) DegreeTwoThreeSpectrum7136.graph sourceMap4770=true := by decide +kernel
theorem fusedMap4770_checked : acceptsGraphIso
    (fused (graph core4770) (root 10) 2 2) DegreeTwoThreeSpectrum6101.graph fusedMap4770=true := by decide +kernel
theorem certified4770 : Certified (graph core4770) (root 10) 2 2 :=
  of_native_maps core4770 DegreeTwoThreeSpectrum7136.graph DegreeTwoThreeSpectrum6101.graph
    sourceMap4770 fusedMap4770 sourceMap4770_checked fusedMap4770_checked
    DegreeTwoThreeFiniteComparisons.comparison4770
#print axioms sourceMap4770_checked
#print axioms fusedMap4770_checked
#print axioms certified4770
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
