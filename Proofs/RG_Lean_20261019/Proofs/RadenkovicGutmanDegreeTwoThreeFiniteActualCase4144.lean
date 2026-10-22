/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4144 : Family 8 := level8.get ⟨155,by decide⟩
def sourceMap4144 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4144 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4144_checked : acceptsGraphIso
    (source (graph core4144) (root 8) 2 2) DegreeTwoThreeSpectrum3576.graph sourceMap4144=true := by decide +kernel
theorem fusedMap4144_checked : acceptsGraphIso
    (fused (graph core4144) (root 8) 2 2) DegreeTwoThreeSpectrum2757.graph fusedMap4144=true := by decide +kernel
theorem certified4144 : Certified (graph core4144) (root 8) 2 2 :=
  of_native_maps core4144 DegreeTwoThreeSpectrum3576.graph DegreeTwoThreeSpectrum2757.graph
    sourceMap4144 fusedMap4144 sourceMap4144_checked fusedMap4144_checked
    DegreeTwoThreeFiniteComparisons.comparison4144
#print axioms sourceMap4144_checked
#print axioms fusedMap4144_checked
#print axioms certified4144
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
