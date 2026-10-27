/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4171 : Family 8 := level8.get ⟨216,by decide⟩
def sourceMap4171 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4171 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4171_checked : acceptsGraphIso
    (source (graph core4171) (root 8) 2 2) DegreeTwoThreeSpectrum3804.graph sourceMap4171=true := by decide +kernel
theorem fusedMap4171_checked : acceptsGraphIso
    (fused (graph core4171) (root 8) 2 2) DegreeTwoThreeSpectrum2522.graph fusedMap4171=true := by decide +kernel
theorem certified4171 : Certified (graph core4171) (root 8) 2 2 :=
  of_native_maps core4171 DegreeTwoThreeSpectrum3804.graph DegreeTwoThreeSpectrum2522.graph
    sourceMap4171 fusedMap4171 sourceMap4171_checked fusedMap4171_checked
    DegreeTwoThreeFiniteComparisons.comparison4171
#print axioms sourceMap4171_checked
#print axioms fusedMap4171_checked
#print axioms certified4171
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
