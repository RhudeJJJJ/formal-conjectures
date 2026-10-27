/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons84
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4225 : Family 9 := level9.get ⟨133,by decide⟩
def sourceMap4225 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4225 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 2 2 v)
theorem sourceMap4225_checked : acceptsGraphIso
    (source (graph core4225) (root 9) 2 2) DegreeTwoThreeSpectrum4539.graph sourceMap4225=true := by decide +kernel
theorem fusedMap4225_checked : acceptsGraphIso
    (fused (graph core4225) (root 9) 2 2) DegreeTwoThreeSpectrum4168.graph fusedMap4225=true := by decide +kernel
theorem certified4225 : Certified (graph core4225) (root 9) 2 2 :=
  of_native_maps core4225 DegreeTwoThreeSpectrum4539.graph DegreeTwoThreeSpectrum4168.graph
    sourceMap4225 fusedMap4225 sourceMap4225_checked fusedMap4225_checked
    DegreeTwoThreeFiniteComparisons.comparison4225
#print axioms sourceMap4225_checked
#print axioms fusedMap4225_checked
#print axioms certified4225
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
