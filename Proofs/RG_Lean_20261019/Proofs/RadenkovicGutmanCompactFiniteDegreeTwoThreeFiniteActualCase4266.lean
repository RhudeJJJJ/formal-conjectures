/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4266 : Family 9 := level9.get ⟨264,by decide⟩
def sourceMap4266 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap4266 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4266_checked : acceptsGraphIso
    (source (graph core4266) (root 9) 2 2) DegreeTwoThreeSpectrum4890.graph sourceMap4266=true := by decide +kernel
theorem fusedMap4266_checked : acceptsGraphIso
    (fused (graph core4266) (root 9) 2 2) DegreeTwoThreeSpectrum4074.graph fusedMap4266=true := by decide +kernel
theorem certified4266 : Certified (graph core4266) (root 9) 2 2 :=
  of_native_maps core4266 DegreeTwoThreeSpectrum4890.graph DegreeTwoThreeSpectrum4074.graph
    sourceMap4266 fusedMap4266 sourceMap4266_checked fusedMap4266_checked
    DegreeTwoThreeFiniteComparisons.comparison4266
#print axioms sourceMap4266_checked
#print axioms fusedMap4266_checked
#print axioms certified4266
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
