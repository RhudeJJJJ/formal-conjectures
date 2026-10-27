/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4509 : Family 10 := level10.get ⟨320,by decide⟩
def sourceMap4509 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4509 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4509_checked : acceptsGraphIso
    (source (graph core4509) (root 10) 2 2) DegreeTwoThreeSpectrum6669.graph sourceMap4509=true := by decide +kernel
theorem fusedMap4509_checked : acceptsGraphIso
    (fused (graph core4509) (root 10) 2 2) DegreeTwoThreeSpectrum5535.graph fusedMap4509=true := by decide +kernel
theorem certified4509 : Certified (graph core4509) (root 10) 2 2 :=
  of_native_maps core4509 DegreeTwoThreeSpectrum6669.graph DegreeTwoThreeSpectrum5535.graph
    sourceMap4509 fusedMap4509 sourceMap4509_checked fusedMap4509_checked
    DegreeTwoThreeFiniteComparisons.comparison4509
#print axioms sourceMap4509_checked
#print axioms fusedMap4509_checked
#print axioms certified4509
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
