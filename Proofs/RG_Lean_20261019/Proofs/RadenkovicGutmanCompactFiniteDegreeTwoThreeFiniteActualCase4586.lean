/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4586 : Family 10 := level10.get ⟨555,by decide⟩
def sourceMap4586 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4586 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4586_checked : acceptsGraphIso
    (source (graph core4586) (root 10) 2 2) DegreeTwoThreeSpectrum7167.graph sourceMap4586=true := by decide +kernel
theorem fusedMap4586_checked : acceptsGraphIso
    (fused (graph core4586) (root 10) 2 2) DegreeTwoThreeSpectrum5213.graph fusedMap4586=true := by decide +kernel
theorem certified4586 : Certified (graph core4586) (root 10) 2 2 :=
  of_native_maps core4586 DegreeTwoThreeSpectrum7167.graph DegreeTwoThreeSpectrum5213.graph
    sourceMap4586 fusedMap4586 sourceMap4586_checked fusedMap4586_checked
    DegreeTwoThreeFiniteComparisons.comparison4586
#print axioms sourceMap4586_checked
#print axioms fusedMap4586_checked
#print axioms certified4586
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
