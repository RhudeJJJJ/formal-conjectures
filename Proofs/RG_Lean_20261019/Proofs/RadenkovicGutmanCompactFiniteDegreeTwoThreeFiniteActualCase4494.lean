/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons89
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4494 : Family 10 := level10.get ⟨269,by decide⟩
def sourceMap4494 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4494 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4494_checked : acceptsGraphIso
    (source (graph core4494) (root 10) 2 2) DegreeTwoThreeSpectrum6450.graph sourceMap4494=true := by decide +kernel
theorem fusedMap4494_checked : acceptsGraphIso
    (fused (graph core4494) (root 10) 2 2) DegreeTwoThreeSpectrum5391.graph fusedMap4494=true := by decide +kernel
theorem certified4494 : Certified (graph core4494) (root 10) 2 2 :=
  of_native_maps core4494 DegreeTwoThreeSpectrum6450.graph DegreeTwoThreeSpectrum5391.graph
    sourceMap4494 fusedMap4494 sourceMap4494_checked fusedMap4494_checked
    DegreeTwoThreeFiniteComparisons.comparison4494
#print axioms sourceMap4494_checked
#print axioms fusedMap4494_checked
#print axioms certified4494
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
