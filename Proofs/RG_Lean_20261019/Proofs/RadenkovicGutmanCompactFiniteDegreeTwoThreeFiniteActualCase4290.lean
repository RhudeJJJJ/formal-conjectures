/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4290 : Family 9 := level9.get ⟨327,by decide⟩
def sourceMap4290 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4290 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4290_checked : acceptsGraphIso
    (source (graph core4290) (root 9) 2 2) DegreeTwoThreeSpectrum4689.graph sourceMap4290=true := by decide +kernel
theorem fusedMap4290_checked : acceptsGraphIso
    (fused (graph core4290) (root 9) 2 2) DegreeTwoThreeSpectrum4199.graph fusedMap4290=true := by decide +kernel
theorem certified4290 : Certified (graph core4290) (root 9) 2 2 :=
  of_native_maps core4290 DegreeTwoThreeSpectrum4689.graph DegreeTwoThreeSpectrum4199.graph
    sourceMap4290 fusedMap4290 sourceMap4290_checked fusedMap4290_checked
    DegreeTwoThreeFiniteComparisons.comparison4290
#print axioms sourceMap4290_checked
#print axioms fusedMap4290_checked
#print axioms certified4290
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
