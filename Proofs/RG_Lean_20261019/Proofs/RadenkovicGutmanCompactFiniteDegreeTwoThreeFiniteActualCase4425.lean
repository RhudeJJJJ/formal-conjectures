/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4425 : Family 9 := level9.get ⟨659,by decide⟩
def sourceMap4425 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,12,13,14,15,6,7,8,9,10,11] (sourceLabel 9 2 2 v)
def fusedMap4425 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4425_checked : acceptsGraphIso
    (source (graph core4425) (root 9) 2 2) DegreeTwoThreeSpectrum4952.graph sourceMap4425=true := by decide +kernel
theorem fusedMap4425_checked : acceptsGraphIso
    (fused (graph core4425) (root 9) 2 2) DegreeTwoThreeSpectrum4459.graph fusedMap4425=true := by decide +kernel
theorem certified4425 : Certified (graph core4425) (root 9) 2 2 :=
  of_native_maps core4425 DegreeTwoThreeSpectrum4952.graph DegreeTwoThreeSpectrum4459.graph
    sourceMap4425 fusedMap4425 sourceMap4425_checked fusedMap4425_checked
    DegreeTwoThreeFiniteComparisons.comparison4425
#print axioms sourceMap4425_checked
#print axioms fusedMap4425_checked
#print axioms certified4425
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
