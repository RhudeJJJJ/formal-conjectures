/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4187 : Family 8 := level8.get ⟨250,by decide⟩
def sourceMap4187 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,11,12,13,14,5,6,7,8,9,10] (sourceLabel 8 2 2 v)
def fusedMap4187 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4187_checked : acceptsGraphIso
    (source (graph core4187) (root 8) 2 2) DegreeTwoThreeSpectrum3847.graph sourceMap4187=true := by decide +kernel
theorem fusedMap4187_checked : acceptsGraphIso
    (fused (graph core4187) (root 8) 2 2) DegreeTwoThreeSpectrum2735.graph fusedMap4187=true := by decide +kernel
theorem certified4187 : Certified (graph core4187) (root 8) 2 2 :=
  of_native_maps core4187 DegreeTwoThreeSpectrum3847.graph DegreeTwoThreeSpectrum2735.graph
    sourceMap4187 fusedMap4187 sourceMap4187_checked fusedMap4187_checked
    DegreeTwoThreeFiniteComparisons.comparison4187
#print axioms sourceMap4187_checked
#print axioms fusedMap4187_checked
#print axioms certified4187
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
