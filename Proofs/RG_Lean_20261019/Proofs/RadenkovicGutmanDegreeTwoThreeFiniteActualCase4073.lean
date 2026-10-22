/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons81
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4073 : Family 7 := level7.get ⟨48,by decide⟩
def sourceMap4073 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![5,0,1,2,3,4,12,13,6,7,8,9,10,11] (sourceLabel 7 2 2 v)
def fusedMap4073 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap4073_checked : acceptsGraphIso
    (source (graph core4073) (root 7) 2 2) DegreeTwoThreeSpectrum2167.graph sourceMap4073=true := by decide +kernel
theorem fusedMap4073_checked : acceptsGraphIso
    (fused (graph core4073) (root 7) 2 2) DegreeTwoThreeSpectrum1845.graph fusedMap4073=true := by decide +kernel
theorem certified4073 : Certified (graph core4073) (root 7) 2 2 :=
  of_native_maps core4073 DegreeTwoThreeSpectrum2167.graph DegreeTwoThreeSpectrum1845.graph
    sourceMap4073 fusedMap4073 sourceMap4073_checked fusedMap4073_checked
    DegreeTwoThreeFiniteComparisons.comparison4073
#print axioms sourceMap4073_checked
#print axioms fusedMap4073_checked
#print axioms certified4073
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
