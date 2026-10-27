/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4289 : Family 9 := level9.get ⟨324,by decide⟩
def sourceMap4289 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4289 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4289_checked : acceptsGraphIso
    (source (graph core4289) (root 9) 2 2) DegreeTwoThreeSpectrum4685.graph sourceMap4289=true := by decide +kernel
theorem fusedMap4289_checked : acceptsGraphIso
    (fused (graph core4289) (root 9) 2 2) DegreeTwoThreeSpectrum4192.graph fusedMap4289=true := by decide +kernel
theorem certified4289 : Certified (graph core4289) (root 9) 2 2 :=
  of_native_maps core4289 DegreeTwoThreeSpectrum4685.graph DegreeTwoThreeSpectrum4192.graph
    sourceMap4289 fusedMap4289 sourceMap4289_checked fusedMap4289_checked
    DegreeTwoThreeFiniteComparisons.comparison4289
#print axioms sourceMap4289_checked
#print axioms fusedMap4289_checked
#print axioms certified4289
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
