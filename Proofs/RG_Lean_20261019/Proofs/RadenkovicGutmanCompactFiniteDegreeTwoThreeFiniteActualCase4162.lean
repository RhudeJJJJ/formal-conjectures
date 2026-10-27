/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4162 : Family 8 := level8.get ⟨198,by decide⟩
def sourceMap4162 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4162 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4162_checked : acceptsGraphIso
    (source (graph core4162) (root 8) 2 2) DegreeTwoThreeSpectrum3766.graph sourceMap4162=true := by decide +kernel
theorem fusedMap4162_checked : acceptsGraphIso
    (fused (graph core4162) (root 8) 2 2) DegreeTwoThreeSpectrum2457.graph fusedMap4162=true := by decide +kernel
theorem certified4162 : Certified (graph core4162) (root 8) 2 2 :=
  of_native_maps core4162 DegreeTwoThreeSpectrum3766.graph DegreeTwoThreeSpectrum2457.graph
    sourceMap4162 fusedMap4162 sourceMap4162_checked fusedMap4162_checked
    DegreeTwoThreeFiniteComparisons.comparison4162
#print axioms sourceMap4162_checked
#print axioms fusedMap4162_checked
#print axioms certified4162
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
