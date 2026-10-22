/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4145 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap4145 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap4145 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4145_checked : acceptsGraphIso
    (source (graph core4145) (root 8) 2 2) DegreeTwoThreeSpectrum3590.graph sourceMap4145=true := by decide +kernel
theorem fusedMap4145_checked : acceptsGraphIso
    (fused (graph core4145) (root 8) 2 2) DegreeTwoThreeSpectrum2774.graph fusedMap4145=true := by decide +kernel
theorem certified4145 : Certified (graph core4145) (root 8) 2 2 :=
  of_native_maps core4145 DegreeTwoThreeSpectrum3590.graph DegreeTwoThreeSpectrum2774.graph
    sourceMap4145 fusedMap4145 sourceMap4145_checked fusedMap4145_checked
    DegreeTwoThreeFiniteComparisons.comparison4145
#print axioms sourceMap4145_checked
#print axioms fusedMap4145_checked
#print axioms certified4145
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
