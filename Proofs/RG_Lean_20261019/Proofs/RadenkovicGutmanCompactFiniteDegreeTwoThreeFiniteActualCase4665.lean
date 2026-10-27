/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4665 : Family 10 := level10.get ⟨786,by decide⟩
def sourceMap4665 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4665 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4665_checked : acceptsGraphIso
    (source (graph core4665) (root 10) 2 2) DegreeTwoThreeSpectrum7454.graph sourceMap4665=true := by decide +kernel
theorem fusedMap4665_checked : acceptsGraphIso
    (fused (graph core4665) (root 10) 2 2) DegreeTwoThreeSpectrum5568.graph fusedMap4665=true := by decide +kernel
theorem certified4665 : Certified (graph core4665) (root 10) 2 2 :=
  of_native_maps core4665 DegreeTwoThreeSpectrum7454.graph DegreeTwoThreeSpectrum5568.graph
    sourceMap4665 fusedMap4665 sourceMap4665_checked fusedMap4665_checked
    DegreeTwoThreeFiniteComparisons.comparison4665
#print axioms sourceMap4665_checked
#print axioms fusedMap4665_checked
#print axioms certified4665
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
