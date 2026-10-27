/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4134 : Family 8 := level8.get ⟨128,by decide⟩
def sourceMap4134 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4134 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4134_checked : acceptsGraphIso
    (source (graph core4134) (root 8) 2 2) DegreeTwoThreeSpectrum3356.graph sourceMap4134=true := by decide +kernel
theorem fusedMap4134_checked : acceptsGraphIso
    (fused (graph core4134) (root 8) 2 2) DegreeTwoThreeSpectrum2605.graph fusedMap4134=true := by decide +kernel
theorem certified4134 : Certified (graph core4134) (root 8) 2 2 :=
  of_native_maps core4134 DegreeTwoThreeSpectrum3356.graph DegreeTwoThreeSpectrum2605.graph
    sourceMap4134 fusedMap4134 sourceMap4134_checked fusedMap4134_checked
    DegreeTwoThreeFiniteComparisons.comparison4134
#print axioms sourceMap4134_checked
#print axioms fusedMap4134_checked
#print axioms certified4134
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
