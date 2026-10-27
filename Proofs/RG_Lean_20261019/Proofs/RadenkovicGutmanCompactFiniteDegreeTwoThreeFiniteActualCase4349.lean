/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4349 : Family 9 := level9.get ⟨474,by decide⟩
def sourceMap4349 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,7,8,9,10,11,12] (sourceLabel 9 2 2 v)
def fusedMap4349 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4349_checked : acceptsGraphIso
    (source (graph core4349) (root 9) 2 2) DegreeTwoThreeSpectrum4852.graph sourceMap4349=true := by decide +kernel
theorem fusedMap4349_checked : acceptsGraphIso
    (fused (graph core4349) (root 9) 2 2) DegreeTwoThreeSpectrum4510.graph fusedMap4349=true := by decide +kernel
theorem certified4349 : Certified (graph core4349) (root 9) 2 2 :=
  of_native_maps core4349 DegreeTwoThreeSpectrum4852.graph DegreeTwoThreeSpectrum4510.graph
    sourceMap4349 fusedMap4349 sourceMap4349_checked fusedMap4349_checked
    DegreeTwoThreeFiniteComparisons.comparison4349
#print axioms sourceMap4349_checked
#print axioms fusedMap4349_checked
#print axioms certified4349
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
