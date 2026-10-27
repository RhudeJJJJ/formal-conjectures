/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons86
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4328 : Family 9 := level9.get ⟨424,by decide⟩
def sourceMap4328 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap4328 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4328_checked : acceptsGraphIso
    (source (graph core4328) (root 9) 2 2) DegreeTwoThreeSpectrum4799.graph sourceMap4328=true := by decide +kernel
theorem fusedMap4328_checked : acceptsGraphIso
    (fused (graph core4328) (root 9) 2 2) DegreeTwoThreeSpectrum4411.graph fusedMap4328=true := by decide +kernel
theorem certified4328 : Certified (graph core4328) (root 9) 2 2 :=
  of_native_maps core4328 DegreeTwoThreeSpectrum4799.graph DegreeTwoThreeSpectrum4411.graph
    sourceMap4328 fusedMap4328 sourceMap4328_checked fusedMap4328_checked
    DegreeTwoThreeFiniteComparisons.comparison4328
#print axioms sourceMap4328_checked
#print axioms fusedMap4328_checked
#print axioms certified4328
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
