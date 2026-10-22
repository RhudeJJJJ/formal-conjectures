/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5017 : Family 10 := level10.get ⟨1657,by decide⟩
def sourceMap5017 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap5017 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5017_checked : acceptsGraphIso
    (source (graph core5017) (root 10) 2 2) DegreeTwoThreeSpectrum7618.graph sourceMap5017=true := by decide +kernel
theorem fusedMap5017_checked : acceptsGraphIso
    (fused (graph core5017) (root 10) 2 2) DegreeTwoThreeSpectrum6258.graph fusedMap5017=true := by decide +kernel
theorem certified5017 : Certified (graph core5017) (root 10) 2 2 :=
  of_native_maps core5017 DegreeTwoThreeSpectrum7618.graph DegreeTwoThreeSpectrum6258.graph
    sourceMap5017 fusedMap5017 sourceMap5017_checked fusedMap5017_checked
    DegreeTwoThreeFiniteComparisons.comparison5017
#print axioms sourceMap5017_checked
#print axioms fusedMap5017_checked
#print axioms certified5017
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
