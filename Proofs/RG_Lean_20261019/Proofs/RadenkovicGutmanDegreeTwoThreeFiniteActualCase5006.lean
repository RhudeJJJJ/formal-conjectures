/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons100
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5006 : Family 10 := level10.get ⟨1634,by decide⟩
def sourceMap5006 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap5006 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap5006_checked : acceptsGraphIso
    (source (graph core5006) (root 10) 2 2) DegreeTwoThreeSpectrum7607.graph sourceMap5006=true := by decide +kernel
theorem fusedMap5006_checked : acceptsGraphIso
    (fused (graph core5006) (root 10) 2 2) DegreeTwoThreeSpectrum6202.graph fusedMap5006=true := by decide +kernel
theorem certified5006 : Certified (graph core5006) (root 10) 2 2 :=
  of_native_maps core5006 DegreeTwoThreeSpectrum7607.graph DegreeTwoThreeSpectrum6202.graph
    sourceMap5006 fusedMap5006 sourceMap5006_checked fusedMap5006_checked
    DegreeTwoThreeFiniteComparisons.comparison5006
#print axioms sourceMap5006_checked
#print axioms fusedMap5006_checked
#print axioms certified5006
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
