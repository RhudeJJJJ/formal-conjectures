/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4630 : Family 10 := level10.get ⟨678,by decide⟩
def sourceMap4630 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,13,14,15,16,7,8,9,10,11,12] (sourceLabel 10 2 2 v)
def fusedMap4630 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4630_checked : acceptsGraphIso
    (source (graph core4630) (root 10) 2 2) DegreeTwoThreeSpectrum7313.graph sourceMap4630=true := by decide +kernel
theorem fusedMap4630_checked : acceptsGraphIso
    (fused (graph core4630) (root 10) 2 2) DegreeTwoThreeSpectrum5401.graph fusedMap4630=true := by decide +kernel
theorem certified4630 : Certified (graph core4630) (root 10) 2 2 :=
  of_native_maps core4630 DegreeTwoThreeSpectrum7313.graph DegreeTwoThreeSpectrum5401.graph
    sourceMap4630 fusedMap4630 sourceMap4630_checked fusedMap4630_checked
    DegreeTwoThreeFiniteComparisons.comparison4630
#print axioms sourceMap4630_checked
#print axioms fusedMap4630_checked
#print axioms certified4630
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
