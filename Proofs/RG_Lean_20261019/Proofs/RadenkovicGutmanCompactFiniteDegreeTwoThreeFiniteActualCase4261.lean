/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4261 : Family 9 := level9.get ⟨247,by decide⟩
def sourceMap4261 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap4261 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4261_checked : acceptsGraphIso
    (source (graph core4261) (root 9) 2 2) DegreeTwoThreeSpectrum4855.graph sourceMap4261=true := by decide +kernel
theorem fusedMap4261_checked : acceptsGraphIso
    (fused (graph core4261) (root 9) 2 2) DegreeTwoThreeSpectrum4048.graph fusedMap4261=true := by decide +kernel
theorem certified4261 : Certified (graph core4261) (root 9) 2 2 :=
  of_native_maps core4261 DegreeTwoThreeSpectrum4855.graph DegreeTwoThreeSpectrum4048.graph
    sourceMap4261 fusedMap4261 sourceMap4261_checked fusedMap4261_checked
    DegreeTwoThreeFiniteComparisons.comparison4261
#print axioms sourceMap4261_checked
#print axioms fusedMap4261_checked
#print axioms certified4261
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
